//! Defines `FaerieBackend`.

use container;
use cretonne_codegen::binemit::{Addend, CodeOffset, Reloc, RelocSink, NullTrapSink};
use cretonne_codegen::isa::TargetIsa;
use cretonne_codegen::result::CtonError;
use cretonne_codegen::{self, binemit, ir};
use cretonne_module::{Backend, DataContext, Linkage, ModuleNamespace, Init, DataDescription};
use faerie;
use failure::Error;
use std::fs::File;
use target;

/// A builder for `FaerieBackend`.
pub struct FaerieBuilder {
    isa: Box<TargetIsa>,
    name: String,
    format: container::Format,
    faerie_target: faerie::Target,
}

impl FaerieBuilder {
    /// Create a new `FaerieBuilder` using the given Cretonne target, that
    /// can be passed to
    /// [`Module::new`](cretonne_module/struct.Module.html#method.new].
    ///
    /// Note: To support calls JIT'd functions from Rust or other compiled
    /// code, it's necessary for the `call_conv` setting in `isa`'s flags
    /// to match the host platform.
    pub fn new(
        isa: Box<TargetIsa>,
        name: String,
        format: container::Format,
    ) -> Result<Self, Error> {
        debug_assert!(isa.flags().is_pic(), "faerie requires PIC");
        let faerie_target = target::translate(&*isa)?;
        Ok(Self {
            isa,
            name,
            format,
            faerie_target,
        })
    }
}

/// A `FaerieBackend` implements `Backend` and emits ".o" files using the `faerie` library.
pub struct FaerieBackend {
    isa: Box<TargetIsa>,
    artifact: faerie::Artifact,
    format: container::Format,
}

pub struct FaerieCompiledFunction {}

pub struct FaerieCompiledData {}

impl Backend for FaerieBackend {
    type Builder = FaerieBuilder;

    type CompiledFunction = FaerieCompiledFunction;
    type CompiledData = FaerieCompiledData;

    // There's no need to return invidual artifacts; we're writing them into
    // the output file instead.
    type FinalizedFunction = ();
    type FinalizedData = ();

    /// The returned value here provides functions for emitting object files
    /// to memory and files.
    type Product = FaerieProduct;

    /// Create a new `FaerieBackend` using the given Cretonne target.
    fn new(builder: FaerieBuilder) -> Self {
        Self {
            isa: builder.isa,
            artifact: faerie::Artifact::new(builder.faerie_target, builder.name),
            format: builder.format,
        }
    }

    fn isa(&self) -> &TargetIsa {
        &*self.isa
    }

    fn declare_function(&mut self, name: &str, linkage: Linkage) {
        self.artifact
            .declare(name, translate_function_linkage(linkage))
            .expect("inconsistent declarations");
    }

    fn declare_data(&mut self, name: &str, linkage: Linkage, writable: bool) {
        self.artifact
            .declare(name, translate_data_linkage(linkage, writable))
            .expect("inconsistent declarations");
    }

    fn define_function(
        &mut self,
        name: &str,
        ctx: &cretonne_codegen::Context,
        namespace: &ModuleNamespace<Self>,
        code_size: u32,
    ) -> Result<FaerieCompiledFunction, CtonError> {
        let mut code: Vec<u8> = Vec::with_capacity(code_size as usize);
        code.resize(code_size as usize, 0);

        // Non-lexical lifetimes would obviate the braces here.
        {
            let mut reloc_sink = FaerieRelocSink {
                format: self.format,
                artifact: &mut self.artifact,
                name,
                namespace,
            };
            // Ignore traps for now. For now, frontends should just avoid generating code
            // that traps.
            let mut trap_sink = NullTrapSink {};

            unsafe {
                ctx.emit_to_memory(
                    &*self.isa,
                    code.as_mut_ptr(),
                    &mut reloc_sink,
                    &mut trap_sink,
                )
            };
        }

        self.artifact.define(name, code).expect(
            "inconsistent declaration",
        );
        Ok(FaerieCompiledFunction {})
    }

    fn define_data(
        &mut self,
        name: &str,
        data_ctx: &DataContext,
        namespace: &ModuleNamespace<Self>,
    ) -> Result<FaerieCompiledData, CtonError> {
        let &DataDescription {
            writable: _writable,
            ref init,
            ref function_decls,
            ref data_decls,
            ref function_relocs,
            ref data_relocs,
        } = data_ctx.description();

        let size = init.size();
        let mut bytes = Vec::with_capacity(size);
        match *init {
            Init::Uninitialized => {
                panic!("data is not initialized yet");
            }
            Init::Zeros { .. } => {
                bytes.resize(size, 0);
            }
            Init::Bytes { ref contents } => {
                bytes.extend_from_slice(contents);
            }
        }

        // TODO: Change the signature of this function to use something other
        // than `CtonError`, as `CtonError` can't convey faerie's errors.
        for &(offset, id) in function_relocs {
            let to = &namespace.get_function_decl(&function_decls[id]).name;
            self.artifact
                .link(faerie::Link {
                    from: name,
                    to,
                    at: offset as usize,
                })
                .map_err(|_e| CtonError::InvalidInput)?;
        }
        for &(offset, id, addend) in data_relocs {
            debug_assert_eq!(
                addend,
                0,
                "faerie doesn't support addends in data section relocations yet"
            );
            let to = &namespace.get_data_decl(&data_decls[id]).name;
            self.artifact
                .link(faerie::Link {
                    from: name,
                    to,
                    at: offset as usize,
                })
                .map_err(|_e| CtonError::InvalidInput)?;
        }

        self.artifact.define(name, bytes).expect(
            "inconsistent declaration",
        );
        Ok(FaerieCompiledData {})
    }

    fn write_data_funcaddr(
        &mut self,
        _data: &mut FaerieCompiledData,
        _offset: usize,
        _what: ir::FuncRef,
    ) {
        unimplemented!()
    }

    fn write_data_dataaddr(
        &mut self,
        _data: &mut FaerieCompiledData,
        _offset: usize,
        _what: ir::GlobalVar,
        _usize: binemit::Addend,
    ) {
        unimplemented!()
    }

    fn finalize_function(
        &mut self,
        _func: &FaerieCompiledFunction,
        _namespace: &ModuleNamespace<Self>,
    ) {
        // Nothing to do.
    }

    fn finalize_data(&mut self, _data: &FaerieCompiledData, _namespace: &ModuleNamespace<Self>) {
        // Nothing to do.
    }

    fn finish(self) -> FaerieProduct {
        FaerieProduct {
            artifact: self.artifact,
            format: self.format,
        }
    }
}

/// This is the output of `Module`'s
/// [`finish`](../cretonne_module/struct.Module.html#method.finish) function.
/// It provides functions for writing out the object file to memory or a file.
pub struct FaerieProduct {
    artifact: faerie::Artifact,
    format: container::Format,
}

impl FaerieProduct {
    /// Return the name of the output file. This is the name passed into `new`.
    pub fn name(&self) -> &str {
        &self.artifact.name
    }

    /// Call `emit` on the faerie `Artifact`, producing bytes in memory.
    pub fn emit(&self) -> Result<Vec<u8>, Error> {
        match self.format {
            container::Format::ELF => self.artifact.emit::<faerie::Elf>(),
            container::Format::MachO => self.artifact.emit::<faerie::Mach>(),
        }
    }

    /// Call `write` on the faerie `Artifact`, writing to a file.
    pub fn write(&self, sink: File) -> Result<(), Error> {
        match self.format {
            container::Format::ELF => self.artifact.write::<faerie::Elf>(sink),
            container::Format::MachO => self.artifact.write::<faerie::Mach>(sink),
        }
    }
}

fn translate_function_linkage(linkage: Linkage) -> faerie::Decl {
    match linkage {
        Linkage::Import => faerie::Decl::FunctionImport,
        Linkage::Local => faerie::Decl::Function { global: false },
        Linkage::Preemptible | Linkage::Export => faerie::Decl::Function { global: true },
    }
}

fn translate_data_linkage(linkage: Linkage, writable: bool) -> faerie::Decl {
    match linkage {
        Linkage::Import => faerie::Decl::DataImport,
        Linkage::Local => {
            faerie::Decl::Data {
                global: false,
                writeable: writable,
            }
        }
        Linkage::Export => {
            faerie::Decl::Data {
                global: true,
                writeable: writable,
            }
        }
        Linkage::Preemptible => {
            unimplemented!("faerie doesn't support preemptible globals yet");
        }
    }
}

struct FaerieRelocSink<'a> {
    format: container::Format,
    artifact: &'a mut faerie::Artifact,
    name: &'a str,
    namespace: &'a ModuleNamespace<'a, FaerieBackend>,
}

impl<'a> RelocSink for FaerieRelocSink<'a> {
    fn reloc_ebb(&mut self, _offset: CodeOffset, _reloc: Reloc, _ebb_offset: CodeOffset) {
        unimplemented!();
    }

    fn reloc_external(
        &mut self,
        offset: CodeOffset,
        reloc: Reloc,
        name: &ir::ExternalName,
        addend: Addend,
    ) {
        let ref_name = if self.namespace.is_function(name) {
            &self.namespace.get_function_decl(name).name
        } else {
            &self.namespace.get_data_decl(name).name
        };
        let addend_i32 = addend as i32;
        debug_assert!(i64::from(addend_i32) == addend);
        let raw_reloc = container::raw_relocation(reloc, self.format);
        self.artifact
            .link_with(
                faerie::Link {
                    from: self.name,
                    to: ref_name,
                    at: offset as usize,
                },
                faerie::RelocOverride {
                    reloc: raw_reloc,
                    addend: addend_i32,
                },
            )
            .expect("faerie relocation error");
    }

    fn reloc_jt(&mut self, _offset: CodeOffset, _reloc: Reloc, _jt: ir::JumpTable) {
        unimplemented!();
    }
}
