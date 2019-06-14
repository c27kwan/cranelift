use crate::cursor::{Cursor, FuncCursor};
use crate::dominator_tree::DominatorTree;
use crate::ir::{Ebb, Function, InstBuilder, Value};
use crate::isa::TargetIsa;
use crate::regalloc::live_value_tracker::LiveValueTracker;
use crate::regalloc::liveness::Liveness;
use std::collections::HashSet;
use std::vec::Vec;

fn get_live_ref_values<'f>(tracker: &mut LiveValueTracker, pos: &FuncCursor<'f>) -> Vec<Value> {
    // Grab the values that are still live
    let live_info = tracker.live();

    // Iterate through all live values, return only the references
    let mut live_ref_values = Vec::new();

    for value_in_list in live_info {
        if pos.func.dfg.value_type(value_in_list.value).is_ref() {
            live_ref_values.push(value_in_list.value);
        }
    }

    live_ref_values
}

fn ins_and_enc_stackmap_instr<'f>(
    pos: &mut FuncCursor<'f>,
    live_ref_values: &Vec<Value>,
    isa: &TargetIsa,
) {
    pos.ins().stackmap(&live_ref_values);
    // Move cursor to the new stackmap instr to encode it
    if let Some(inst) = pos.prev_inst() {
        let ok = pos.func.update_encoding(inst, isa).is_ok();
        debug_assert!(ok);
    }
    // Restore cursor position
    pos.next_inst();
}

fn try_insert_savepoint_at_ebb_top<'f>(
    ebb: Ebb,
    pos: &mut FuncCursor<'f>,
    liveness: &Liveness,
    domtree: &DominatorTree,
    tracker: &mut LiveValueTracker,
    dest_ebbs: &HashSet<Ebb>,
    isa: &TargetIsa,
) {
    // Analyse liveness of variables from the top of ebb
    tracker.ebb_top(ebb, &pos.func.dfg, liveness, &pos.func.layout, domtree);
    tracker.drop_dead_params();

    let live_ref_values = get_live_ref_values(tracker, &pos);

    // If the current ebb is in the hashset, there is a jump to this cursor pos
    // from an instruction positioned further down in layout. All loops will lead
    // to such a jump (the converse is not true), so insert stackmap here.
    if dest_ebbs.contains(&ebb) && !live_ref_values.is_empty() {
        pos.goto_first_inst(ebb);
        ins_and_enc_stackmap_instr(pos, &live_ref_values, isa);
    }
}

// The emit_stackmaps() function analyzes each instruction to retrieve the liveness of
// the defs and operands by traversing a function's ebbs in reverse layout order.
pub fn emit_stackmaps(
    func: &mut Function,
    domtree: &DominatorTree,
    liveness: &Liveness,
    tracker: &mut LiveValueTracker,
    isa: &TargetIsa,
) {
    let mut dest_ebbs: HashSet<Ebb> = HashSet::new();
    let mut curr = func.layout.last_ebb();

    // Visit EBBs in reverse layout order
    while let Some(ebb) = curr {
        let mut self_loop = false;
        let mut pos = FuncCursor::new(func);

        try_insert_savepoint_at_ebb_top(ebb, &mut pos, liveness, domtree, tracker, &dest_ebbs, isa);

        // From the top of the ebb, step through the instructions
        pos.goto_top(ebb);

        while let Some(inst) = pos.next_inst() {
            let live_ref_values = get_live_ref_values(tracker, &pos);

            // Get opcode of instruction
            let opcode = pos.func.dfg[inst].opcode();

            // Process the instruction
            tracker.process_inst(inst, &pos.func.dfg, liveness);

            // Get rid of values that have either (1) Dead Definitions or (2) Killed by Inst
            tracker.drop_dead(inst);

            if let Some(dest) = pos.func.dfg[inst].branch_destination() {
                // Loop within ebb, but savepoint instr was never added. Flag to handle this at the end.
                if dest == ebb && !dest_ebbs.contains(&ebb) {
                    self_loop = true;
                }
                // Add destination branch to hashset
                dest_ebbs.insert(dest);
            } else if opcode.is_call() && !live_ref_values.is_empty() {
                ins_and_enc_stackmap_instr(&mut pos, &live_ref_values, isa);
            }
        }
        if self_loop {
            try_insert_savepoint_at_ebb_top(
                ebb, &mut pos, liveness, domtree, tracker, &dest_ebbs, isa,
            );
        }
        curr = func.layout.prev_ebb(ebb);
    }
}
