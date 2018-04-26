//! Source map associating entities with their source locations.
//!
//! When the parser reads in a source file, it records the locations of the
//! definitions of entities like instructions, EBBs, and values.
//!
//! The `SourceMap` struct defined in this module makes this mapping available
//! to parser clients.

use cretonne_codegen::ir::entities::AnyEntity;
use cretonne_codegen::ir::{Ebb, FuncRef, GlobalVar, Heap, JumpTable, SigRef, StackSlot, Value};
use error::{Location, Result};
use lexer::split_entity_name;
use std::collections::HashMap;

/// Mapping from entity names to source locations.
#[derive(Debug, Default)]
pub struct SourceMap {
    // Store locations for entities, including instructions.
    locations: HashMap<AnyEntity, Location>,
}

/// Read-only interface which is exposed outside the parser crate.
impl SourceMap {
    /// Look up a value entity.
    pub fn contains_value(&self, v: Value) -> bool {
        self.locations.contains_key(&v.into())
    }

    /// Look up a EBB entity.
    pub fn contains_ebb(&self, ebb: Ebb) -> bool {
        self.locations.contains_key(&ebb.into())
    }

    /// Look up a stack slot entity.
    pub fn contains_ss(&self, ss: StackSlot) -> bool {
        self.locations.contains_key(&ss.into())
    }

    /// Look up a global variable entity.
    pub fn contains_gv(&self, gv: GlobalVar) -> bool {
        self.locations.contains_key(&gv.into())
    }

    /// Look up a heap entity.
    pub fn contains_heap(&self, heap: Heap) -> bool {
        self.locations.contains_key(&heap.into())
    }

    /// Look up a signature entity.
    pub fn contains_sig(&self, sig: SigRef) -> bool {
        self.locations.contains_key(&sig.into())
    }

    /// Look up a function entity.
    pub fn contains_fn(&self, fn_: FuncRef) -> bool {
        self.locations.contains_key(&fn_.into())
    }

    /// Look up a jump table entity.
    pub fn contains_jt(&self, jt: JumpTable) -> bool {
        self.locations.contains_key(&jt.into())
    }

    /// Look up an entity by source name.
    /// Returns the entity reference corresponding to `name`, if it exists.
    pub fn lookup_str(&self, name: &str) -> Option<AnyEntity> {
        split_entity_name(name).and_then(|(ent, num)| match ent {
            "v" => {
                Value::with_number(num).and_then(|v| if !self.contains_value(v) {
                    None
                } else {
                    Some(v.into())
                })
            }
            "ebb" => {
                Ebb::with_number(num).and_then(|ebb| if !self.contains_ebb(ebb) {
                    None
                } else {
                    Some(ebb.into())
                })
            }
            "ss" => {
                StackSlot::with_number(num).and_then(|ss| if !self.contains_ss(ss) {
                    None
                } else {
                    Some(ss.into())
                })
            }
            "gv" => {
                GlobalVar::with_number(num).and_then(|gv| if !self.contains_gv(gv) {
                    None
                } else {
                    Some(gv.into())
                })
            }
            "heap" => {
                Heap::with_number(num).and_then(|heap| if !self.contains_heap(heap) {
                    None
                } else {
                    Some(heap.into())
                })
            }
            "sig" => {
                SigRef::with_number(num).and_then(|sig| if !self.contains_sig(sig) {
                    None
                } else {
                    Some(sig.into())
                })
            }
            "fn" => {
                FuncRef::with_number(num).and_then(|fn_| if !self.contains_fn(fn_) {
                    None
                } else {
                    Some(fn_.into())
                })
            }
            "jt" => {
                JumpTable::with_number(num).and_then(|jt| if !self.contains_jt(jt) {
                    None
                } else {
                    Some(jt.into())
                })
            }
            _ => None,
        })
    }

    /// Get the source location where an entity was defined.
    pub fn location(&self, entity: AnyEntity) -> Option<Location> {
        self.locations.get(&entity).cloned()
    }
}

impl SourceMap {
    /// Create a new empty `SourceMap`.
    pub fn new() -> Self {
        Self { locations: HashMap::new() }
    }

    /// Define the value `entity`.
    pub fn def_value(&mut self, entity: Value, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the ebb `entity`.
    pub fn def_ebb(&mut self, entity: Ebb, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the stack slot `entity`.
    pub fn def_ss(&mut self, entity: StackSlot, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the global variable `entity`.
    pub fn def_gv(&mut self, entity: GlobalVar, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the heap `entity`.
    pub fn def_heap(&mut self, entity: Heap, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the signature `entity`.
    pub fn def_sig(&mut self, entity: SigRef, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the external function `entity`.
    pub fn def_fn(&mut self, entity: FuncRef, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define the jump table `entity`.
    pub fn def_jt(&mut self, entity: JumpTable, loc: &Location) -> Result<()> {
        self.def_entity(entity.into(), loc)
    }

    /// Define an entity. This can be used for instructions whose numbers never
    /// appear in source, or implicitly defined signatures.
    pub fn def_entity(&mut self, entity: AnyEntity, loc: &Location) -> Result<()> {
        if self.locations.insert(entity, *loc).is_some() {
            err!(loc, "duplicate entity: {}", entity)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use parse_test;

    #[test]
    fn details() {
        let tf = parse_test(
            "function %detail() {
                               ss10 = incoming_arg 13
                               jt10 = jump_table ebb0
                             ebb0(v4: i32, v7: i32):
                               v10 = iadd v4, v7
                             }",
        ).unwrap();
        let map = &tf.functions[0].1.map;

        assert_eq!(map.lookup_str("v0"), None);
        assert_eq!(map.lookup_str("ss1"), None);
        assert_eq!(map.lookup_str("ss10").unwrap().to_string(), "ss10");
        assert_eq!(map.lookup_str("jt10").unwrap().to_string(), "jt10");
        assert_eq!(map.lookup_str("ebb0").unwrap().to_string(), "ebb0");
        assert_eq!(map.lookup_str("v4").unwrap().to_string(), "v4");
        assert_eq!(map.lookup_str("v7").unwrap().to_string(), "v7");
        assert_eq!(map.lookup_str("v10").unwrap().to_string(), "v10");
    }
}
