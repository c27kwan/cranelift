//! Verify CPU flags values.

use entity::{EntityMap, SparseSet};
use flowgraph::ControlFlowGraph;
use ir;
use ir::instructions::BranchInfo;
use isa;
use packed_option::PackedOption;
use std::result;
use timing;
use verifier::{Error, Result};

/// Verify that CPU flags are used correctly.
///
/// The value types `iflags` and `fflags` represent CPU flags which usually live in a
/// special-purpose register, so they can't be used as freely as other value types that can live in
/// any register.
///
/// We verify the following conditions:
///
/// - At most one flags value can be live at a time.
/// - A flags value can not be live across an instruction that clobbers the flags.
///
///
pub fn verify_flags(
    func: &ir::Function,
    cfg: &ControlFlowGraph,
    isa: Option<&isa::TargetIsa>,
) -> Result {
    let _tt = timing::verify_flags();
    let mut verifier = FlagsVerifier {
        func,
        cfg,
        encinfo: isa.map(|isa| isa.encoding_info()),
        livein: EntityMap::new(),
    };
    verifier.check()
}

struct FlagsVerifier<'a> {
    func: &'a ir::Function,
    cfg: &'a ControlFlowGraph,
    encinfo: Option<isa::EncInfo>,

    /// The single live-in flags value (if any) for each EBB.
    livein: EntityMap<ir::Ebb, PackedOption<ir::Value>>,
}

impl<'a> FlagsVerifier<'a> {
    fn check(&mut self) -> Result {
        // List of EBBs that need to be processed. EBBs may be re-added to this list when we detect
        // that one of their successor blocks needs a live-in flags value.
        let mut worklist = SparseSet::new();
        for ebb in self.func.layout.ebbs() {
            worklist.insert(ebb);
        }

        while let Some(ebb) = worklist.pop() {
            if let Some(value) = self.visit_ebb(ebb)? {
                // The EBB has live-in flags. Check if the value changed.
                match self.livein[ebb].expand() {
                    // Revisit any predecessor blocks the first time we see a live-in for `ebb`.
                    None => {
                        self.livein[ebb] = value.into();
                        for (pred, _) in self.cfg.pred_iter(ebb) {
                            worklist.insert(pred);
                        }
                    }
                    Some(old) if old != value => {
                        return err!(ebb, "conflicting live-in CPU flags: {} and {}", old, value);
                    }
                    x => assert_eq!(x, Some(value)),
                }
            } else {
                // Existing live-in flags should never be able to disappear.
                assert_eq!(self.livein[ebb].expand(), None);
            }
        }

        Ok(())
    }

    /// Check flags usage in `ebb` and return the live-in flags value, if any.
    fn visit_ebb(&self, ebb: ir::Ebb) -> result::Result<Option<ir::Value>, Error> {
        // The single currently live flags value.
        let mut live_val = None;

        // Visit instructions backwards so we can track liveness accurately.
        for inst in self.func.layout.ebb_insts(ebb).rev() {
            // Check if `inst` interferes with existing live flags.
            if let Some(live) = live_val {
                for &res in self.func.dfg.inst_results(inst) {
                    if res == live {
                        // We've reached the def of `live_flags`, so it is no longer live above.
                        live_val = None;
                    } else if self.func.dfg.value_type(res).is_flags() {
                        return err!(inst, "{} clobbers live CPU flags in {}", res, live);
                    }
                }

                // Does the instruction have an encoding that clobbers the CPU flags?
                if self.encinfo
                    .as_ref()
                    .and_then(|ei| ei.operand_constraints(self.func.encodings[inst]))
                    .map_or(false, |c| c.clobbers_flags) && live_val.is_some()
                {
                    return err!(inst, "encoding clobbers live CPU flags in {}", live);
                }
            }

            // Now look for live ranges of CPU flags that end here.
            for &arg in self.func.dfg.inst_args(inst) {
                if self.func.dfg.value_type(arg).is_flags() {
                    merge(&mut live_val, arg, inst)?;
                }
            }

            // Include live-in flags to successor EBBs.
            match self.func.dfg.analyze_branch(inst) {
                BranchInfo::NotABranch => {}
                BranchInfo::SingleDest(dest, _) => {
                    if let Some(val) = self.livein[dest].expand() {
                        merge(&mut live_val, val, inst)?;
                    }
                }
                BranchInfo::Table(jt) => {
                    for (_, dest) in self.func.jump_tables[jt].entries() {
                        if let Some(val) = self.livein[dest].expand() {
                            merge(&mut live_val, val, inst)?;
                        }
                    }
                }
            }
        }

        // Return the required live-in flags value.
        Ok(live_val)
    }
}

// Merge live flags values, or return an error on conflicting values.
fn merge(a: &mut Option<ir::Value>, b: ir::Value, inst: ir::Inst) -> Result {
    if let Some(va) = *a {
        if b != va {
            return err!(inst, "conflicting live CPU flags: {} and {}", va, b);
        }
    } else {
        *a = Some(b);
    }

    Ok(())
}
