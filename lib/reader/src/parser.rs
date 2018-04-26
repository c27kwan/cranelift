//! Parser for .cton files.

use cretonne_codegen::entity::EntityRef;
use cretonne_codegen::ir;
use cretonne_codegen::ir::entities::AnyEntity;
use cretonne_codegen::ir::immediates::{Ieee32, Ieee64, Imm64, Offset32, Uimm32};
use cretonne_codegen::ir::instructions::{InstructionData, InstructionFormat, VariableArgs};
use cretonne_codegen::ir::types::VOID;
use cretonne_codegen::ir::{AbiParam, ArgumentExtension, ArgumentLoc, Ebb, ExtFuncData,
                           ExternalName, FuncRef, Function, GlobalVar, GlobalVarData, Heap,
                           HeapBase, HeapData, HeapStyle, JumpTable, JumpTableData, MemFlags,
                           Opcode, SigRef, Signature, StackSlot, StackSlotData, StackSlotKind,
                           Type, Value, ValueLoc};
use cretonne_codegen::isa::{self, Encoding, RegUnit, TargetIsa};
use cretonne_codegen::packed_option::ReservedValue;
use cretonne_codegen::{settings, timing};
use cretonne_codegen::settings::CallConv;
use error::{Error, Location, Result};
use isaspec;
use lexer::{self, Lexer, Token};
use sourcemap::SourceMap;
use std::mem;
use std::str::FromStr;
use std::{u16, u32};
use testcommand::TestCommand;
use testfile::{Comment, Details, TestFile};

/// Parse the entire `text` into a list of functions.
///
/// Any test commands or ISA declarations are ignored.
pub fn parse_functions(text: &str) -> Result<Vec<Function>> {
    let _tt = timing::parse_text();
    parse_test(text).map(|file| {
        file.functions.into_iter().map(|(func, _)| func).collect()
    })
}

/// Parse the entire `text` as a test case file.
///
/// The returned `TestFile` contains direct references to substrings of `text`.
pub fn parse_test(text: &str) -> Result<TestFile> {
    let _tt = timing::parse_text();
    let mut parser = Parser::new(text);
    // Gather the preamble comments.
    parser.start_gathering_comments();

    let commands = parser.parse_test_commands();
    let isa_spec = parser.parse_isa_specs()?;

    parser.token();
    parser.claim_gathered_comments(AnyEntity::Function);

    let preamble_comments = parser.take_comments();
    let functions = parser.parse_function_list(isa_spec.unique_isa())?;

    Ok(TestFile {
        commands,
        isa_spec,
        preamble_comments,
        functions,
    })
}

pub struct Parser<'a> {
    lex: Lexer<'a>,

    lex_error: Option<lexer::Error>,

    /// Current lookahead token.
    lookahead: Option<Token<'a>>,

    /// Location of lookahead.
    loc: Location,

    /// Are we gathering any comments that we encounter?
    gathering_comments: bool,

    /// The gathered comments; claim them with `claim_gathered_comments`.
    gathered_comments: Vec<&'a str>,

    /// Comments collected so far.
    comments: Vec<Comment<'a>>,
}

/// Context for resolving references when parsing a single function.
struct Context<'a> {
    function: Function,
    map: SourceMap,

    /// Aliases to resolve once value definitions are known.
    aliases: Vec<Value>,

    /// Reference to the unique_isa for things like parsing ISA-specific instruction encoding
    /// information. This is only `Some` if exactly one set of `isa` directives were found in the
    /// prologue (it is valid to have directives for multiple different ISAs, but in that case we
    /// couldn't know which ISA the provided encodings are intended for)
    unique_isa: Option<&'a TargetIsa>,
}

impl<'a> Context<'a> {
    fn new(f: Function, unique_isa: Option<&'a TargetIsa>) -> Context<'a> {
        Context {
            function: f,
            map: SourceMap::new(),
            unique_isa,
            aliases: Vec::new(),
        }
    }

    // Get the index of a recipe name if it exists.
    fn find_recipe_index(&self, recipe_name: &str) -> Option<u16> {
        if let Some(unique_isa) = self.unique_isa {
            unique_isa
                .encoding_info()
                .names
                .iter()
                .position(|&name| name == recipe_name)
                .map(|idx| idx as u16)
        } else {
            None
        }
    }

    // Allocate a new stack slot.
    fn add_ss(&mut self, ss: StackSlot, data: StackSlotData, loc: &Location) -> Result<()> {
        while self.function.stack_slots.next_key().index() <= ss.index() {
            self.function.create_stack_slot(
                StackSlotData::new(StackSlotKind::SpillSlot, 0),
            );
        }
        self.function.stack_slots[ss] = data;
        self.map.def_ss(ss, loc)
    }

    // Resolve a reference to a stack slot.
    fn check_ss(&self, ss: StackSlot, loc: &Location) -> Result<()> {
        if !self.map.contains_ss(ss) {
            err!(loc, "undefined stack slot {}", ss)
        } else {
            Ok(())
        }
    }

    // Allocate a global variable slot.
    fn add_gv(&mut self, gv: GlobalVar, data: GlobalVarData, loc: &Location) -> Result<()> {
        while self.function.global_vars.next_key().index() <= gv.index() {
            self.function.create_global_var(GlobalVarData::Sym {
                name: ExternalName::testcase(""),
                colocated: false,
            });
        }
        self.function.global_vars[gv] = data;
        self.map.def_gv(gv, loc)
    }

    // Resolve a reference to a global variable.
    fn check_gv(&self, gv: GlobalVar, loc: &Location) -> Result<()> {
        if !self.map.contains_gv(gv) {
            err!(loc, "undefined global variable {}", gv)
        } else {
            Ok(())
        }
    }

    // Allocate a heap slot.
    fn add_heap(&mut self, heap: Heap, data: HeapData, loc: &Location) -> Result<()> {
        while self.function.heaps.next_key().index() <= heap.index() {
            self.function.create_heap(HeapData {
                base: HeapBase::ReservedReg,
                min_size: Imm64::new(0),
                guard_size: Imm64::new(0),
                style: HeapStyle::Static { bound: Imm64::new(0) },
            });
        }
        self.function.heaps[heap] = data;
        self.map.def_heap(heap, loc)
    }

    // Resolve a reference to a heap.
    fn check_heap(&self, heap: Heap, loc: &Location) -> Result<()> {
        if !self.map.contains_heap(heap) {
            err!(loc, "undefined heap {}", heap)
        } else {
            Ok(())
        }
    }

    // Allocate a new signature.
    fn add_sig(&mut self, sig: SigRef, data: Signature, loc: &Location) -> Result<()> {
        while self.function.dfg.signatures.next_key().index() <= sig.index() {
            self.function.import_signature(
                Signature::new(CallConv::Fast),
            );
        }
        self.function.dfg.signatures[sig] = data;
        self.map.def_sig(sig, loc)
    }

    // Resolve a reference to a signature.
    fn check_sig(&self, sig: SigRef, loc: &Location) -> Result<()> {
        if !self.map.contains_sig(sig) {
            err!(loc, "undefined signature {}", sig)
        } else {
            Ok(())
        }
    }

    // Allocate a new external function.
    fn add_fn(&mut self, fn_: FuncRef, data: ExtFuncData, loc: &Location) -> Result<()> {
        while self.function.dfg.ext_funcs.next_key().index() <= fn_.index() {
            self.function.import_function(ExtFuncData {
                name: ExternalName::testcase(""),
                signature: SigRef::reserved_value(),
                colocated: false,
            });
        }
        self.function.dfg.ext_funcs[fn_] = data;
        self.map.def_fn(fn_, loc)
    }

    // Resolve a reference to a function.
    fn check_fn(&self, fn_: FuncRef, loc: &Location) -> Result<()> {
        if !self.map.contains_fn(fn_) {
            err!(loc, "undefined function {}", fn_)
        } else {
            Ok(())
        }
    }

    // Allocate a new jump table.
    fn add_jt(&mut self, jt: JumpTable, data: JumpTableData, loc: &Location) -> Result<()> {
        while self.function.jump_tables.next_key().index() <= jt.index() {
            self.function.create_jump_table(JumpTableData::new());
        }
        self.function.jump_tables[jt] = data;
        self.map.def_jt(jt, loc)
    }

    // Resolve a reference to a jump table.
    fn check_jt(&self, jt: JumpTable, loc: &Location) -> Result<()> {
        if !self.map.contains_jt(jt) {
            err!(loc, "undefined jump table {}", jt)
        } else {
            Ok(())
        }
    }

    // Allocate a new EBB.
    fn add_ebb(&mut self, ebb: Ebb, loc: &Location) -> Result<Ebb> {
        while self.function.dfg.num_ebbs() <= ebb.index() {
            self.function.dfg.make_ebb();
        }
        self.function.layout.append_ebb(ebb);
        self.map.def_ebb(ebb, loc).and(Ok(ebb))
    }
}

impl<'a> Parser<'a> {
    /// Create a new `Parser` which reads `text`. The referenced text must outlive the parser.
    pub fn new(text: &'a str) -> Parser {
        Parser {
            lex: Lexer::new(text),
            lex_error: None,
            lookahead: None,
            loc: Location { line_number: 0 },
            gathering_comments: false,
            gathered_comments: Vec::new(),
            comments: Vec::new(),
        }
    }

    // Consume the current lookahead token and return it.
    fn consume(&mut self) -> Token<'a> {
        self.lookahead.take().expect("No token to consume")
    }

    // Consume the whole line following the current lookahead token.
    // Return the text of the line tail.
    fn consume_line(&mut self) -> &'a str {
        let rest = self.lex.rest_of_line();
        self.consume();
        rest
    }

    // Get the current lookahead token, after making sure there is one.
    fn token(&mut self) -> Option<Token<'a>> {
        // clippy says self.lookahead is immutable so this loop is either infinite or never
        // running. I don't think this is true - self.lookahead is mutated in the loop body - so
        // maybe this is a clippy bug? Either way, disable clippy for this.
        #[cfg_attr(feature = "cargo-clippy", allow(while_immutable_condition))]
        while self.lookahead == None {
            match self.lex.next() {
                Some(Ok(lexer::LocatedToken { token, location })) => {
                    match token {
                        Token::Comment(text) => {
                            if self.gathering_comments {
                                self.gathered_comments.push(text);
                            }
                        }
                        _ => self.lookahead = Some(token),
                    }
                    self.loc = location;
                }
                Some(Err(lexer::LocatedError { error, location })) => {
                    self.lex_error = Some(error);
                    self.loc = location;
                    break;
                }
                None => break,
            }
        }
        self.lookahead
    }

    // Enable gathering of all comments encountered.
    fn start_gathering_comments(&mut self) {
        debug_assert!(!self.gathering_comments);
        self.gathering_comments = true;
        debug_assert!(self.gathered_comments.is_empty());
    }

    // Claim the comments gathered up to the current position for the
    // given entity.
    fn claim_gathered_comments<E: Into<AnyEntity>>(&mut self, entity: E) {
        debug_assert!(self.gathering_comments);
        let entity = entity.into();
        self.comments.extend(
            self.gathered_comments.drain(..).map(|text| {
                Comment { entity, text }
            }),
        );
        self.gathering_comments = false;
    }

    // Get the comments collected so far, clearing out the internal list.
    fn take_comments(&mut self) -> Vec<Comment<'a>> {
        debug_assert!(!self.gathering_comments);
        mem::replace(&mut self.comments, Vec::new())
    }

    // Match and consume a token without payload.
    fn match_token(&mut self, want: Token<'a>, err_msg: &str) -> Result<Token<'a>> {
        if self.token() == Some(want) {
            Ok(self.consume())
        } else {
            err!(self.loc, err_msg)
        }
    }

    // If the next token is a `want`, consume it, otherwise do nothing.
    fn optional(&mut self, want: Token<'a>) -> bool {
        if self.token() == Some(want) {
            self.consume();
            true
        } else {
            false
        }
    }

    // Match and consume a specific identifier string.
    // Used for pseudo-keywords like "stack_slot" that only appear in certain contexts.
    fn match_identifier(&mut self, want: &'static str, err_msg: &str) -> Result<Token<'a>> {
        if self.token() == Some(Token::Identifier(want)) {
            Ok(self.consume())
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a type.
    fn match_type(&mut self, err_msg: &str) -> Result<Type> {
        if let Some(Token::Type(t)) = self.token() {
            self.consume();
            Ok(t)
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a stack slot reference.
    fn match_ss(&mut self, err_msg: &str) -> Result<StackSlot> {
        if let Some(Token::StackSlot(ss)) = self.token() {
            self.consume();
            if let Some(ss) = StackSlot::with_number(ss) {
                return Ok(ss);
            }
        }
        err!(self.loc, err_msg)
    }

    // Match and consume a global variable reference.
    fn match_gv(&mut self, err_msg: &str) -> Result<GlobalVar> {
        if let Some(Token::GlobalVar(gv)) = self.token() {
            self.consume();
            if let Some(gv) = GlobalVar::with_number(gv) {
                return Ok(gv);
            }
        }
        err!(self.loc, err_msg)
    }

    // Match and consume a function reference.
    fn match_fn(&mut self, err_msg: &str) -> Result<FuncRef> {
        if let Some(Token::FuncRef(fnref)) = self.token() {
            self.consume();
            if let Some(fnref) = FuncRef::with_number(fnref) {
                return Ok(fnref);
            }
        }
        err!(self.loc, err_msg)
    }

    // Match and consume a signature reference.
    fn match_sig(&mut self, err_msg: &str) -> Result<SigRef> {
        if let Some(Token::SigRef(sigref)) = self.token() {
            self.consume();
            if let Some(sigref) = SigRef::with_number(sigref) {
                return Ok(sigref);
            }
        }
        err!(self.loc, err_msg)
    }

    // Match and consume a heap reference.
    fn match_heap(&mut self, err_msg: &str) -> Result<Heap> {
        if let Some(Token::Heap(heap)) = self.token() {
            self.consume();
            if let Some(heap) = Heap::with_number(heap) {
                return Ok(heap);
            }
        }
        err!(self.loc, err_msg)
    }

    // Match and consume a jump table reference.
    fn match_jt(&mut self) -> Result<JumpTable> {
        if let Some(Token::JumpTable(jt)) = self.token() {
            self.consume();
            if let Some(jt) = JumpTable::with_number(jt) {
                return Ok(jt);
            }
        }
        err!(self.loc, "expected jump table number: jt«n»")
    }

    // Match and consume an ebb reference.
    fn match_ebb(&mut self, err_msg: &str) -> Result<Ebb> {
        if let Some(Token::Ebb(ebb)) = self.token() {
            self.consume();
            Ok(ebb)
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a value reference, direct or vtable.
    fn match_value(&mut self, err_msg: &str) -> Result<Value> {
        if let Some(Token::Value(v)) = self.token() {
            self.consume();
            Ok(v)
        } else {
            err!(self.loc, err_msg)
        }
    }

    fn error(&self, message: &str) -> Error {
        Error {
            location: self.loc,
            message: message.to_string(),
        }
    }

    // Match and consume an Imm64 immediate.
    fn match_imm64(&mut self, err_msg: &str) -> Result<Imm64> {
        if let Some(Token::Integer(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like an integer.
            // Parse it as an Imm64 to check for overflow and other issues.
            text.parse().map_err(|e| self.error(e))
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a Uimm32 immediate.
    fn match_uimm32(&mut self, err_msg: &str) -> Result<Uimm32> {
        if let Some(Token::Integer(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like an integer.
            // Parse it as an Uimm32 to check for overflow and other issues.
            text.parse().map_err(|e| self.error(e))
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a u8 immediate.
    // This is used for lane numbers in SIMD vectors.
    fn match_uimm8(&mut self, err_msg: &str) -> Result<u8> {
        if let Some(Token::Integer(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like an integer.
            // Parse it as a u8 to check for overflow and other issues.
            text.parse().map_err(
                |_| self.error("expected u8 decimal immediate"),
            )
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume an i32 immediate.
    // This is used for stack argument byte offsets.
    fn match_imm32(&mut self, err_msg: &str) -> Result<i32> {
        if let Some(Token::Integer(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like an integer.
            // Parse it as a i32 to check for overflow and other issues.
            text.parse().map_err(
                |_| self.error("expected i32 decimal immediate"),
            )
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume an optional offset32 immediate.
    //
    // Note that this will match an empty string as an empty offset, and that if an offset is
    // present, it must contain a sign.
    fn optional_offset32(&mut self) -> Result<Offset32> {
        if let Some(Token::Integer(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like an integer.
            // Parse it as an `Offset32` to check for overflow and other issues.
            text.parse().map_err(|e| self.error(e))
        } else {
            // An offset32 operand can be absent.
            Ok(Offset32::new(0))
        }
    }

    // Match and consume an Ieee32 immediate.
    fn match_ieee32(&mut self, err_msg: &str) -> Result<Ieee32> {
        if let Some(Token::Float(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like a float.
            // Parse it as an Ieee32 to check for the right number of digits and other issues.
            text.parse().map_err(|e| self.error(e))
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume an Ieee64 immediate.
    fn match_ieee64(&mut self, err_msg: &str) -> Result<Ieee64> {
        if let Some(Token::Float(text)) = self.token() {
            self.consume();
            // Lexer just gives us raw text that looks like a float.
            // Parse it as an Ieee64 to check for the right number of digits and other issues.
            text.parse().map_err(|e| self.error(e))
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a boolean immediate.
    fn match_bool(&mut self, err_msg: &str) -> Result<bool> {
        if let Some(Token::Identifier(text)) = self.token() {
            self.consume();
            match text {
                "true" => Ok(true),
                "false" => Ok(false),
                _ => err!(self.loc, err_msg),
            }
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume an enumerated immediate, like one of the condition codes.
    fn match_enum<T: FromStr>(&mut self, err_msg: &str) -> Result<T> {
        if let Some(Token::Identifier(text)) = self.token() {
            self.consume();
            text.parse().map_err(|_| self.error(err_msg))
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and a consume a possibly empty sequence of memory operation flags.
    fn optional_memflags(&mut self) -> MemFlags {
        let mut flags = MemFlags::new();
        while let Some(Token::Identifier(text)) = self.token() {
            if flags.set_by_name(text) {
                self.consume();
            } else {
                break;
            }
        }
        flags
    }

    // Match and consume an identifier.
    fn match_any_identifier(&mut self, err_msg: &str) -> Result<&'a str> {
        if let Some(Token::Identifier(text)) = self.token() {
            self.consume();
            Ok(text)
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a HexSequence that fits into a u16.
    // This is used for instruction encodings.
    fn match_hex16(&mut self, err_msg: &str) -> Result<u16> {
        if let Some(Token::HexSequence(bits_str)) = self.token() {
            self.consume();
            // The only error we anticipate from this parse is overflow, the lexer should
            // already have ensured that the string doesn't contain invalid characters, and
            // isn't empty or negative.
            u16::from_str_radix(bits_str, 16).map_err(|_| {
                self.error("the hex sequence given overflows the u16 type")
            })
        } else {
            err!(self.loc, err_msg)
        }
    }

    // Match and consume a register unit either by number `%15` or by name `%rax`.
    fn match_regunit(&mut self, isa: Option<&TargetIsa>) -> Result<RegUnit> {
        if let Some(Token::Name(name)) = self.token() {
            self.consume();
            match isa {
                Some(isa) => {
                    isa.register_info().parse_regunit(name).ok_or_else(|| {
                        self.error("invalid register name")
                    })
                }
                None => {
                    name.parse().map_err(
                        |_| self.error("invalid register number"),
                    )
                }
            }
        } else {
            match isa {
                Some(isa) => err!(self.loc, "Expected {} register unit", isa.name()),
                None => err!(self.loc, "Expected register unit number"),
            }
        }
    }

    /// Parse an optional source location.
    ///
    /// Return an optional source location if no real location is present.
    fn optional_srcloc(&mut self) -> Result<ir::SourceLoc> {
        if let Some(Token::SourceLoc(text)) = self.token() {
            match u32::from_str_radix(text, 16) {
                Ok(num) => {
                    self.consume();
                    Ok(ir::SourceLoc::new(num))
                }
                Err(_) => return err!(self.loc, "invalid source location: {}", text),
            }
        } else {
            Ok(Default::default())
        }
    }

    /// Parse a list of test commands.
    pub fn parse_test_commands(&mut self) -> Vec<TestCommand<'a>> {
        let mut list = Vec::new();
        while self.token() == Some(Token::Identifier("test")) {
            list.push(TestCommand::new(self.consume_line()));
        }
        list
    }

    /// Parse a list of ISA specs.
    ///
    /// Accept a mix of `isa` and `set` command lines. The `set` commands are cumulative.
    ///
    pub fn parse_isa_specs(&mut self) -> Result<isaspec::IsaSpec> {
        // Was there any `isa` commands?
        let mut seen_isa = false;
        // Location of last `set` command since the last `isa`.
        let mut last_set_loc = None;

        let mut isas = Vec::new();
        let mut flag_builder = settings::builder();

        while let Some(Token::Identifier(command)) = self.token() {
            match command {
                "set" => {
                    last_set_loc = Some(self.loc);
                    isaspec::parse_options(
                        self.consume_line().trim().split_whitespace(),
                        &mut flag_builder,
                        &self.loc,
                    )?;
                }
                "isa" => {
                    let loc = self.loc;
                    // Grab the whole line so the lexer won't go looking for tokens on the
                    // following lines.
                    let mut words = self.consume_line().trim().split_whitespace();
                    // Look for `isa foo`.
                    let isa_name = match words.next() {
                        None => return err!(loc, "expected ISA name"),
                        Some(w) => w,
                    };
                    let mut isa_builder = match isa::lookup(isa_name) {
                        Err(isa::LookupError::Unknown) => {
                            return err!(loc, "unknown ISA '{}'", isa_name)
                        }
                        Err(isa::LookupError::Unsupported) => {
                            continue;
                        }
                        Ok(b) => b,
                    };
                    last_set_loc = None;
                    seen_isa = true;
                    // Apply the ISA-specific settings to `isa_builder`.
                    isaspec::parse_options(words, &mut isa_builder, &self.loc)?;

                    // Construct a trait object with the aggregate settings.
                    isas.push(isa_builder.finish(settings::Flags::new(&flag_builder)));
                }
                _ => break,
            }
        }
        if !seen_isa {
            // No `isa` commands, but we allow for `set` commands.
            Ok(isaspec::IsaSpec::None(settings::Flags::new(&flag_builder)))
        } else if let Some(loc) = last_set_loc {
            err!(
                loc,
                "dangling 'set' command after ISA specification has no effect."
            )
        } else {
            Ok(isaspec::IsaSpec::Some(isas))
        }
    }

    /// Parse a list of function definitions.
    ///
    /// This is the top-level parse function matching the whole contents of a file.
    pub fn parse_function_list(
        &mut self,
        unique_isa: Option<&TargetIsa>,
    ) -> Result<Vec<(Function, Details<'a>)>> {
        let mut list = Vec::new();
        while self.token().is_some() {
            list.push(self.parse_function(unique_isa)?);
        }
        if let Some(err) = self.lex_error {
            return match err {
                lexer::Error::InvalidChar => err!(self.loc, "invalid character"),
            };
        }
        Ok(list)
    }

    // Parse a whole function definition.
    //
    // function ::= * "function" name signature "{" preamble function-body "}"
    //
    fn parse_function(
        &mut self,
        unique_isa: Option<&TargetIsa>,
    ) -> Result<(Function, Details<'a>)> {
        // Begin gathering comments.
        // Make sure we don't include any comments before the `function` keyword.
        self.token();
        debug_assert!(self.comments.is_empty());
        self.start_gathering_comments();

        self.match_identifier("function", "expected 'function'")?;

        let location = self.loc;

        // function ::= "function" * name signature "{" preamble function-body "}"
        let name = self.parse_external_name()?;

        // function ::= "function" name * signature "{" preamble function-body "}"
        let sig = self.parse_signature(unique_isa)?;

        let mut ctx = Context::new(Function::with_name_signature(name, sig), unique_isa);

        // function ::= "function" name signature * "{" preamble function-body "}"
        self.match_token(
            Token::LBrace,
            "expected '{' before function body",
        )?;

        self.token();
        self.claim_gathered_comments(AnyEntity::Function);

        // function ::= "function" name signature "{" * preamble function-body "}"
        self.parse_preamble(&mut ctx)?;
        // function ::= "function" name signature "{"  preamble * function-body "}"
        self.parse_function_body(&mut ctx)?;
        // function ::= "function" name signature "{" preamble function-body * "}"
        self.match_token(
            Token::RBrace,
            "expected '}' after function body",
        )?;

        // Collect any comments following the end of the function, then stop gathering comments.
        self.start_gathering_comments();
        self.token();
        self.claim_gathered_comments(AnyEntity::Function);

        let details = Details {
            location,
            comments: self.take_comments(),
            map: ctx.map,
        };

        Ok((ctx.function, details))
    }

    // Parse an external name.
    //
    // For example, in a function decl, the parser would be in this state:
    //
    // function ::= "function" * name signature { ... }
    //
    fn parse_external_name(&mut self) -> Result<ExternalName> {
        match self.token() {
            Some(Token::Name(s)) => {
                self.consume();
                s.parse().map_err(
                    |_| self.error("invalid test case or libcall name"),
                )
            }
            Some(Token::UserRef(namespace)) => {
                self.consume();
                match self.token() {
                    Some(Token::Colon) => {
                        self.consume();
                        match self.token() {
                            Some(Token::Integer(index_str)) => {
                                let index: u32 = u32::from_str_radix(index_str, 10).map_err(|_| {
                                    self.error("the integer given overflows the u32 type")
                                })?;
                                self.consume();
                                Ok(ExternalName::user(namespace, index))
                            }
                            _ => err!(self.loc, "expected integer"),
                        }
                    }
                    _ => err!(self.loc, "expected colon"),
                }
            }
            _ => err!(self.loc, "expected external name"),
        }
    }

    // Parse a function signature.
    //
    // signature ::=  * "(" [paramlist] ")" ["->" retlist] [callconv]
    //
    fn parse_signature(&mut self, unique_isa: Option<&TargetIsa>) -> Result<Signature> {
        // Calling convention defaults to `fast`, but can be changed.
        let mut sig = Signature::new(CallConv::Fast);

        self.match_token(
            Token::LPar,
            "expected function signature: ( args... )",
        )?;
        // signature ::=  "(" * [abi-param-list] ")" ["->" retlist] [callconv]
        if self.token() != Some(Token::RPar) {
            sig.params = self.parse_abi_param_list(unique_isa)?;
        }
        self.match_token(
            Token::RPar,
            "expected ')' after function arguments",
        )?;
        if self.optional(Token::Arrow) {
            sig.returns = self.parse_abi_param_list(unique_isa)?;
        }

        // The calling convention is optional.
        if let Some(Token::Identifier(text)) = self.token() {
            match text.parse() {
                Ok(cc) => {
                    self.consume();
                    sig.call_conv = cc;
                }
                _ => return err!(self.loc, "unknown calling convention: {}", text),
            }
        }

        if sig.params.iter().all(|a| a.location.is_assigned()) {
            sig.compute_argument_bytes();
        }

        Ok(sig)
    }

    // Parse list of function parameter / return value types.
    //
    // paramlist ::= * param { "," param }
    //
    fn parse_abi_param_list(&mut self, unique_isa: Option<&TargetIsa>) -> Result<Vec<AbiParam>> {
        let mut list = Vec::new();

        // abi-param-list ::= * abi-param { "," abi-param }
        list.push(self.parse_abi_param(unique_isa)?);

        // abi-param-list ::= abi-param * { "," abi-param }
        while self.optional(Token::Comma) {
            // abi-param-list ::= abi-param { "," * abi-param }
            list.push(self.parse_abi_param(unique_isa)?);
        }

        Ok(list)
    }

    // Parse a single argument type with flags.
    fn parse_abi_param(&mut self, unique_isa: Option<&TargetIsa>) -> Result<AbiParam> {
        // abi-param ::= * type { flag } [ argumentloc ]
        let mut arg = AbiParam::new(self.match_type("expected parameter type")?);

        // abi-param ::= type * { flag } [ argumentloc ]
        while let Some(Token::Identifier(s)) = self.token() {
            match s {
                "uext" => arg.extension = ArgumentExtension::Uext,
                "sext" => arg.extension = ArgumentExtension::Sext,
                _ => {
                    if let Ok(purpose) = s.parse() {
                        arg.purpose = purpose;
                    } else {
                        break;
                    }
                }
            }
            self.consume();
        }

        // abi-param ::= type { flag } * [ argumentloc ]
        arg.location = self.parse_argument_location(unique_isa)?;

        Ok(arg)
    }

    // Parse an argument location specifier; either a register or a byte offset into the stack.
    fn parse_argument_location(&mut self, unique_isa: Option<&TargetIsa>) -> Result<ArgumentLoc> {
        // argumentloc ::= '[' regname | uimm32 ']'
        if self.optional(Token::LBracket) {
            let result = match self.token() {
                Some(Token::Name(name)) => {
                    self.consume();
                    if let Some(isa) = unique_isa {
                        isa.register_info()
                            .parse_regunit(name)
                            .map(ArgumentLoc::Reg)
                            .ok_or_else(|| self.error("invalid register name"))
                    } else {
                        err!(self.loc, "argument location requires exactly one isa")
                    }
                }
                Some(Token::Integer(_)) => {
                    let offset = self.match_imm32("expected stack argument byte offset")?;
                    Ok(ArgumentLoc::Stack(offset))
                }
                Some(Token::Minus) => {
                    self.consume();
                    Ok(ArgumentLoc::Unassigned)
                }
                _ => err!(self.loc, "expected argument location"),
            };

            self.match_token(
                Token::RBracket,
                "expected ']' to end argument location annotation",
            )?;

            result
        } else {
            Ok(ArgumentLoc::Unassigned)
        }
    }

    // Parse the function preamble.
    //
    // preamble      ::= * { preamble-decl }
    // preamble-decl ::= * stack-slot-decl
    //                   * function-decl
    //                   * signature-decl
    //                   * jump-table-decl
    //
    // The parsed decls are added to `ctx` rather than returned.
    fn parse_preamble(&mut self, ctx: &mut Context) -> Result<()> {
        loop {
            match self.token() {
                Some(Token::StackSlot(..)) => {
                    self.start_gathering_comments();
                    let loc = self.loc;
                    self.parse_stack_slot_decl().and_then(|(ss, dat)| {
                        ctx.add_ss(ss, dat, &loc)
                    })
                }
                Some(Token::GlobalVar(..)) => {
                    self.start_gathering_comments();
                    self.parse_global_var_decl().and_then(|(gv, dat)| {
                        ctx.add_gv(gv, dat, &self.loc)
                    })
                }
                Some(Token::Heap(..)) => {
                    self.start_gathering_comments();
                    self.parse_heap_decl().and_then(|(heap, dat)| {
                        ctx.add_heap(heap, dat, &self.loc)
                    })
                }
                Some(Token::SigRef(..)) => {
                    self.start_gathering_comments();
                    self.parse_signature_decl(ctx.unique_isa).and_then(
                        |(sig, dat)| {
                            ctx.add_sig(sig, dat, &self.loc)
                        },
                    )
                }
                Some(Token::FuncRef(..)) => {
                    self.start_gathering_comments();
                    self.parse_function_decl(ctx).and_then(|(fn_, dat)| {
                        ctx.add_fn(fn_, dat, &self.loc)
                    })
                }
                Some(Token::JumpTable(..)) => {
                    self.start_gathering_comments();
                    self.parse_jump_table_decl().and_then(|(jt, dat)| {
                        ctx.add_jt(jt, dat, &self.loc)
                    })
                }
                // More to come..
                _ => return Ok(()),
            }?;
        }
    }

    // Parse a stack slot decl.
    //
    // stack-slot-decl ::= * StackSlot(ss) "=" stack-slot-kind Bytes {"," stack-slot-flag}
    // stack-slot-kind ::= "explicit_slot"
    //                   | "spill_slot"
    //                   | "incoming_arg"
    //                   | "outgoing_arg"
    fn parse_stack_slot_decl(&mut self) -> Result<(StackSlot, StackSlotData)> {
        let ss = self.match_ss("expected stack slot number: ss«n»")?;
        self.match_token(
            Token::Equal,
            "expected '=' in stack slot declaration",
        )?;
        let kind = self.match_enum("expected stack slot kind")?;

        // stack-slot-decl ::= StackSlot(ss) "=" stack-slot-kind * Bytes {"," stack-slot-flag}
        let bytes: i64 = self.match_imm64("expected byte-size in stack_slot decl")?
            .into();
        if bytes < 0 {
            return err!(self.loc, "negative stack slot size");
        }
        if bytes > i64::from(u32::MAX) {
            return err!(self.loc, "stack slot too large");
        }
        let mut data = StackSlotData::new(kind, bytes as u32);

        // Take additional options.
        while self.optional(Token::Comma) {
            match self.match_any_identifier("expected stack slot flags")? {
                "offset" => data.offset = Some(self.match_imm32("expected byte offset")?),
                other => return err!(self.loc, "Unknown stack slot flag '{}'", other),
            }
        }

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(ss);

        // TBD: stack-slot-decl ::= StackSlot(ss) "=" stack-slot-kind Bytes * {"," stack-slot-flag}
        Ok((ss, data))
    }

    // Parse a global variable decl.
    //
    // global-var-decl ::= * GlobalVar(gv) "=" global-var-desc
    // global-var-desc ::= "vmctx" offset32
    //                   | "deref" "(" GlobalVar(base) ")" offset32
    //                   | globalsym ["colocated"] name
    //
    fn parse_global_var_decl(&mut self) -> Result<(GlobalVar, GlobalVarData)> {
        let gv = self.match_gv("expected global variable number: gv«n»")?;

        self.match_token(
            Token::Equal,
            "expected '=' in global variable declaration",
        )?;

        let data = match self.match_any_identifier("expected global variable kind")? {
            "vmctx" => {
                let offset = self.optional_offset32()?;
                GlobalVarData::VMContext { offset }
            }
            "deref" => {
                self.match_token(
                    Token::LPar,
                    "expected '(' in 'deref' global variable decl",
                )?;
                let base = self.match_gv("expected global variable: gv«n»")?;
                self.match_token(
                    Token::RPar,
                    "expected ')' in 'deref' global variable decl",
                )?;
                let offset = self.optional_offset32()?;
                GlobalVarData::Deref { base, offset }
            }
            "globalsym" => {
                let colocated = self.optional(Token::Identifier("colocated"));
                let name = self.parse_external_name()?;
                GlobalVarData::Sym { name, colocated }
            }
            other => return err!(self.loc, "Unknown global variable kind '{}'", other),
        };

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(gv);

        Ok((gv, data))
    }

    // Parse a heap decl.
    //
    // heap-decl ::= * Heap(heap) "=" heap-desc
    // heap-desc ::= heap-style heap-base { "," heap-attr }
    // heap-style ::= "static" | "dynamic"
    // heap-base ::= "reserved_reg"
    //             | GlobalVar(base)
    // heap-attr ::= "min" Imm64(bytes)
    //             | "max" Imm64(bytes)
    //             | "guard" Imm64(bytes)
    //
    fn parse_heap_decl(&mut self) -> Result<(Heap, HeapData)> {
        let heap = self.match_heap("expected heap number: heap«n»")?;
        self.match_token(
            Token::Equal,
            "expected '=' in heap declaration",
        )?;

        let style_name = self.match_any_identifier("expected 'static' or 'dynamic'")?;

        // heap-desc ::= heap-style * heap-base { "," heap-attr }
        // heap-base ::= * "reserved_reg"
        //             | * GlobalVar(base)
        let base = match self.token() {
            Some(Token::Identifier("reserved_reg")) => HeapBase::ReservedReg,
            Some(Token::GlobalVar(base_num)) => {
                let base_gv = match GlobalVar::with_number(base_num) {
                    Some(gv) => gv,
                    None => return err!(self.loc, "invalid global variable number for heap base"),
                };
                HeapBase::GlobalVar(base_gv)
            }
            _ => return err!(self.loc, "expected heap base"),
        };
        self.consume();

        let mut data = HeapData {
            base,
            min_size: 0.into(),
            guard_size: 0.into(),
            style: HeapStyle::Static { bound: 0.into() },
        };

        // heap-desc ::= heap-style heap-base * { "," heap-attr }
        while self.optional(Token::Comma) {
            match self.match_any_identifier("expected heap attribute name")? {
                "min" => {
                    data.min_size = self.match_imm64("expected integer min size")?;
                }
                "bound" => {
                    data.style = match style_name {
                        "dynamic" => HeapStyle::Dynamic {
                            bound_gv: self.match_gv("expected gv bound")?,
                        },
                        "static" => HeapStyle::Static {
                            bound: self.match_imm64("expected integer bound")?,
                        },
                        t => return err!(self.loc, "unknown heap style '{}'", t),
                    };
                }
                "guard" => {
                    data.guard_size = self.match_imm64("expected integer guard size")?;
                }
                t => return err!(self.loc, "unknown heap attribute '{}'", t),
            }
        }

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(heap);

        Ok((heap, data))
    }

    // Parse a signature decl.
    //
    // signature-decl ::= SigRef(sigref) "=" signature
    //
    fn parse_signature_decl(
        &mut self,
        unique_isa: Option<&TargetIsa>,
    ) -> Result<(SigRef, Signature)> {
        let sig = self.match_sig("expected signature number: sig«n»")?;
        self.match_token(
            Token::Equal,
            "expected '=' in signature decl",
        )?;
        let data = self.parse_signature(unique_isa)?;

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(sig);

        Ok((sig, data))
    }

    // Parse a function decl.
    //
    // Two variants:
    //
    // function-decl ::= FuncRef(fnref) "=" ["colocated"]" name function-decl-sig
    // function-decl-sig ::= SigRef(sig) | signature
    //
    // The first variant allocates a new signature reference. The second references an existing
    // signature which must be declared first.
    //
    fn parse_function_decl(&mut self, ctx: &mut Context) -> Result<(FuncRef, ExtFuncData)> {
        let fn_ = self.match_fn("expected function number: fn«n»")?;
        self.match_token(
            Token::Equal,
            "expected '=' in function decl",
        )?;

        let loc = self.loc;

        // function-decl ::= FuncRef(fnref) "=" * ["colocated"] name function-decl-sig
        let colocated = self.optional(Token::Identifier("colocated"));

        // function-decl ::= FuncRef(fnref) "=" ["colocated"] * name function-decl-sig
        let name = self.parse_external_name()?;

        // function-decl ::= FuncRef(fnref) "=" ["colocated"] name * function-decl-sig
        let data = match self.token() {
            Some(Token::LPar) => {
                // function-decl ::= FuncRef(fnref) "=" ["colocated"] name * signature
                let sig = self.parse_signature(ctx.unique_isa)?;
                let sigref = ctx.function.import_signature(sig);
                ctx.map.def_entity(sigref.into(), &loc).expect(
                    "duplicate SigRef entities created",
                );
                ExtFuncData {
                    name,
                    signature: sigref,
                    colocated,
                }
            }
            Some(Token::SigRef(sig_src)) => {
                let sig = match SigRef::with_number(sig_src) {
                    None => {
                        return err!(self.loc, "attempted to use invalid signature ss{}", sig_src)
                    }
                    Some(sig) => sig,
                };
                ctx.check_sig(sig, &self.loc)?;
                self.consume();
                ExtFuncData {
                    name,
                    signature: sig,
                    colocated,
                }
            }
            _ => return err!(self.loc, "expected 'function' or sig«n» in function decl"),
        };

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(fn_);

        Ok((fn_, data))
    }

    // Parse a jump table decl.
    //
    // jump-table-decl ::= * JumpTable(jt) "=" "jump_table" jt-entry {"," jt-entry}
    fn parse_jump_table_decl(&mut self) -> Result<(JumpTable, JumpTableData)> {
        let jt = self.match_jt()?;
        self.match_token(
            Token::Equal,
            "expected '=' in jump_table decl",
        )?;
        self.match_identifier("jump_table", "expected 'jump_table'")?;

        let mut data = JumpTableData::new();

        // jump-table-decl ::= JumpTable(jt) "=" "jump_table" * jt-entry {"," jt-entry}
        for idx in 0_usize.. {
            if let Some(dest) = self.parse_jump_table_entry()? {
                data.set_entry(idx, dest);
            }
            if !self.optional(Token::Comma) {
                // Collect any trailing comments.
                self.token();
                self.claim_gathered_comments(jt);

                return Ok((jt, data));
            }
        }

        err!(self.loc, "jump_table too long")
    }

    // jt-entry ::= * Ebb(dest) | "0"
    fn parse_jump_table_entry(&mut self) -> Result<Option<Ebb>> {
        match self.token() {
            Some(Token::Integer(s)) => {
                if s == "0" {
                    self.consume();
                    Ok(None)
                } else {
                    err!(self.loc, "invalid jump_table entry '{}'", s)
                }
            }
            Some(Token::Ebb(dest)) => {
                self.consume();
                Ok(Some(dest))
            }
            _ => err!(self.loc, "expected jump_table entry"),
        }
    }

    // Parse a function body, add contents to `ctx`.
    //
    // function-body ::= * { extended-basic-block }
    //
    fn parse_function_body(&mut self, ctx: &mut Context) -> Result<()> {
        while self.token() != Some(Token::RBrace) {
            self.parse_extended_basic_block(ctx)?;
        }

        // Now that we've seen all defined values in the function, ensure that
        // all references refer to a definition.
        for ebb in &ctx.function.layout {
            for inst in ctx.function.layout.ebb_insts(ebb) {
                for value in ctx.function.dfg.inst_args(inst) {
                    if !ctx.map.contains_value(*value) {
                        return err!(
                            ctx.map.location(AnyEntity::Inst(inst)).unwrap(),
                            "undefined operand value {}",
                            value
                        );
                    }
                }
            }
        }

        for alias in &ctx.aliases {
            if !ctx.function.dfg.set_alias_type_for_parser(*alias) {
                let loc = ctx.map.location(AnyEntity::Value(*alias)).unwrap();
                return err!(loc, "alias cycle involving {}", alias);
            }
        }

        Ok(())
    }

    // Parse an extended basic block, add contents to `ctx`.
    //
    // extended-basic-block ::= * ebb-header { instruction }
    // ebb-header           ::= Ebb(ebb) [ebb-params] ":"
    //
    fn parse_extended_basic_block(&mut self, ctx: &mut Context) -> Result<()> {
        // Collect comments for the next ebb.
        self.start_gathering_comments();

        let ebb_num = self.match_ebb("expected EBB header")?;
        let ebb = ctx.add_ebb(ebb_num, &self.loc)?;

        if !self.optional(Token::Colon) {
            // ebb-header ::= Ebb(ebb) [ * ebb-params ] ":"
            self.parse_ebb_params(ctx, ebb)?;
            self.match_token(
                Token::Colon,
                "expected ':' after EBB parameters",
            )?;
        }

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(ebb);

        // extended-basic-block ::= ebb-header * { instruction }
        while match self.token() {
            Some(Token::Value(_)) |
            Some(Token::Identifier(_)) |
            Some(Token::LBracket) |
            Some(Token::SourceLoc(_)) => true,
            _ => false,
        }
        {
            let srcloc = self.optional_srcloc()?;
            let (encoding, result_locations) = self.parse_instruction_encoding(ctx)?;

            // We need to parse instruction results here because they are shared
            // between the parsing of value aliases and the parsing of instructions.
            //
            // inst-results ::= Value(v) { "," Value(v) }
            let results = self.parse_inst_results()?;

            for result in &results {
                while ctx.function.dfg.num_values() <= result.index() {
                    ctx.function.dfg.make_invalid_value_for_parser();
                }
            }

            match self.token() {
                Some(Token::Arrow) => {
                    self.consume();
                    self.parse_value_alias(&results, ctx)?;
                }
                Some(Token::Equal) => {
                    self.consume();
                    self.parse_instruction(
                        &results,
                        srcloc,
                        encoding,
                        result_locations,
                        ctx,
                        ebb,
                    )?;
                }
                _ if !results.is_empty() => return err!(self.loc, "expected -> or ="),
                _ => {
                    self.parse_instruction(
                        &results,
                        srcloc,
                        encoding,
                        result_locations,
                        ctx,
                        ebb,
                    )?
                }
            }
        }

        Ok(())
    }

    // Parse parenthesized list of EBB parameters. Returns a vector of (u32, Type) pairs with the
    // value numbers of the defined values and the defined types.
    //
    // ebb-params ::= * "(" ebb-param { "," ebb-param } ")"
    fn parse_ebb_params(&mut self, ctx: &mut Context, ebb: Ebb) -> Result<()> {
        // ebb-params ::= * "(" ebb-param { "," ebb-param } ")"
        self.match_token(
            Token::LPar,
            "expected '(' before EBB parameters",
        )?;

        // ebb-params ::= "(" * ebb-param { "," ebb-param } ")"
        self.parse_ebb_param(ctx, ebb)?;

        // ebb-params ::= "(" ebb-param * { "," ebb-param } ")"
        while self.optional(Token::Comma) {
            // ebb-params ::= "(" ebb-param { "," * ebb-param } ")"
            self.parse_ebb_param(ctx, ebb)?;
        }

        // ebb-params ::= "(" ebb-param { "," ebb-param } * ")"
        self.match_token(
            Token::RPar,
            "expected ')' after EBB parameters",
        )?;

        Ok(())
    }

    // Parse a single EBB parameter declaration, and append it to `ebb`.
    //
    // ebb-param ::= * Value(v) ":" Type(t) arg-loc?
    // arg-loc ::= "[" value-location "]"
    //
    fn parse_ebb_param(&mut self, ctx: &mut Context, ebb: Ebb) -> Result<()> {
        // ebb-param ::= * Value(v) ":" Type(t) arg-loc?
        let v = self.match_value("EBB argument must be a value")?;
        let v_location = self.loc;
        // ebb-param ::= Value(v) * ":" Type(t) arg-loc?
        self.match_token(
            Token::Colon,
            "expected ':' after EBB argument",
        )?;
        // ebb-param ::= Value(v) ":" * Type(t) arg-loc?

        while ctx.function.dfg.num_values() <= v.index() {
            ctx.function.dfg.make_invalid_value_for_parser();
        }

        let t = self.match_type("expected EBB argument type")?;
        // Allocate the EBB argument.
        ctx.function.dfg.append_ebb_param_for_parser(ebb, t, v);
        ctx.map.def_value(v, &v_location)?;

        // ebb-param ::= Value(v) ":" Type(t) * arg-loc?
        if self.optional(Token::LBracket) {
            let loc = self.parse_value_location(ctx)?;
            ctx.function.locations[v] = loc;
            self.match_token(
                Token::RBracket,
                "expected ']' after value location",
            )?;
        }

        Ok(())
    }

    fn parse_value_location(&mut self, ctx: &Context) -> Result<ValueLoc> {
        match self.token() {
            Some(Token::StackSlot(src_num)) => {
                self.consume();
                let ss = match StackSlot::with_number(src_num) {
                    None => {
                        return err!(
                            self.loc,
                            "attempted to use invalid stack slot ss{}",
                            src_num
                        )
                    }
                    Some(ss) => ss,
                };
                ctx.check_ss(ss, &self.loc)?;
                Ok(ValueLoc::Stack(ss))
            }
            Some(Token::Name(name)) => {
                self.consume();
                if let Some(isa) = ctx.unique_isa {
                    isa.register_info()
                        .parse_regunit(name)
                        .map(ValueLoc::Reg)
                        .ok_or_else(|| self.error("invalid register value location"))
                } else {
                    err!(self.loc, "value location requires exactly one isa")
                }
            }
            Some(Token::Minus) => {
                self.consume();
                Ok(ValueLoc::Unassigned)
            }
            _ => err!(self.loc, "invalid value location"),
        }
    }

    fn parse_instruction_encoding(
        &mut self,
        ctx: &Context,
    ) -> Result<(Option<Encoding>, Option<Vec<ValueLoc>>)> {
        let (mut encoding, mut result_locations) = (None, None);

        // encoding ::= "[" encoding_literal result_locations "]"
        if self.optional(Token::LBracket) {
            // encoding_literal ::= "-" | Identifier HexSequence
            if !self.optional(Token::Minus) {
                let recipe = self.match_any_identifier(
                    "expected instruction encoding or '-'",
                )?;
                let bits = self.match_hex16("expected a hex sequence")?;

                if let Some(recipe_index) = ctx.find_recipe_index(recipe) {
                    encoding = Some(Encoding::new(recipe_index, bits));
                } else if ctx.unique_isa.is_some() {
                    return err!(self.loc, "invalid instruction recipe");
                } else {
                    // We allow encodings to be specified when there's no unique ISA purely
                    // for convenience, eg when copy-pasting code for a test.
                }
            }

            // result_locations ::= ("," ( "-" | names ) )?
            // names ::= Name { "," Name }
            if self.optional(Token::Comma) {
                let mut results = Vec::new();

                results.push(self.parse_value_location(ctx)?);
                while self.optional(Token::Comma) {
                    results.push(self.parse_value_location(ctx)?);
                }

                result_locations = Some(results);
            }

            self.match_token(
                Token::RBracket,
                "expected ']' to terminate instruction encoding",
            )?;
        }

        Ok((encoding, result_locations))
    }

    // Parse instruction results and return them.
    //
    // inst-results ::= Value(v) { "," Value(v) }
    //
    fn parse_inst_results(&mut self) -> Result<Vec<Value>> {
        // Result value numbers.
        let mut results = Vec::new();

        // instruction  ::=  * [inst-results "="] Opcode(opc) ["." Type] ...
        // inst-results ::= * Value(v) { "," Value(v) }
        if let Some(Token::Value(v)) = self.token() {
            self.consume();

            results.push(v);

            // inst-results ::= Value(v) * { "," Value(v) }
            while self.optional(Token::Comma) {
                // inst-results ::= Value(v) { "," * Value(v) }
                results.push(self.match_value("expected result value")?);
            }
        }

        Ok(results)
    }

    // Parse a value alias, and append it to `ebb`.
    //
    // value_alias ::= [inst-results] "->" Value(v)
    //
    fn parse_value_alias(&mut self, results: &[Value], ctx: &mut Context) -> Result<()> {
        if results.len() != 1 {
            return err!(self.loc, "wrong number of aliases");
        }
        let dest = self.match_value("expected value alias")?;

        ctx.function.dfg.make_value_alias_for_parser(
            dest,
            results[0],
        );
        ctx.map.def_value(results[0], &self.loc)?;
        ctx.aliases.push(results[0]);
        Ok(())
    }

    // Parse an instruction, append it to `ebb`.
    //
    // instruction ::= [inst-results "="] Opcode(opc) ["." Type] ...
    //
    fn parse_instruction(
        &mut self,
        results: &[Value],
        srcloc: ir::SourceLoc,
        encoding: Option<Encoding>,
        result_locations: Option<Vec<ValueLoc>>,
        ctx: &mut Context,
        ebb: Ebb,
    ) -> Result<()> {
        // Define the result values.
        for val in results {
            ctx.map.def_value(*val, &self.loc)?;
        }

        // Collect comments for the next instruction.
        self.start_gathering_comments();

        // instruction ::=  [inst-results "="] * Opcode(opc) ["." Type] ...
        let opcode = if let Some(Token::Identifier(text)) = self.token() {
            match text.parse() {
                Ok(opc) => opc,
                Err(msg) => return err!(self.loc, "{}: '{}'", msg, text),
            }
        } else {
            return err!(self.loc, "expected instruction opcode");
        };
        let opcode_loc = self.loc;
        self.consume();

        // Look for a controlling type variable annotation.
        // instruction ::=  [inst-results "="] Opcode(opc) * ["." Type] ...
        let explicit_ctrl_type = if self.optional(Token::Dot) {
            Some(self.match_type("expected type after 'opcode.'")?)
        } else {
            None
        };

        // instruction ::=  [inst-results "="] Opcode(opc) ["." Type] * ...
        let inst_data = self.parse_inst_operands(ctx, opcode)?;

        // We're done parsing the instruction now.
        //
        // We still need to check that the number of result values in the source matches the opcode
        // or function call signature. We also need to create values with the right type for all
        // the instruction results.
        let ctrl_typevar = self.infer_typevar(
            ctx,
            opcode,
            explicit_ctrl_type,
            &inst_data,
        )?;
        let inst = ctx.function.dfg.make_inst(inst_data);
        let num_results = ctx.function.dfg.make_inst_results_for_parser(
            inst,
            ctrl_typevar,
            results,
        );
        ctx.function.layout.append_inst(inst, ebb);
        ctx.map.def_entity(inst.into(), &opcode_loc).expect(
            "duplicate inst references created",
        );

        if !srcloc.is_default() {
            ctx.function.srclocs[inst] = srcloc;
        }

        if let Some(encoding) = encoding {
            ctx.function.encodings[inst] = encoding;
        }

        if results.len() != num_results {
            return err!(
                self.loc,
                "instruction produces {} result values, {} given",
                num_results,
                results.len()
            );
        }

        if let Some(ref result_locations) = result_locations {
            if results.len() != result_locations.len() {
                return err!(
                    self.loc,
                    "instruction produces {} result values, but {} locations were \
                     specified",
                    results.len(),
                    result_locations.len()
                );
            }
        }

        if let Some(result_locations) = result_locations {
            for (&value, loc) in ctx.function.dfg.inst_results(inst).iter().zip(
                result_locations,
            )
            {
                ctx.function.locations[value] = loc;
            }
        }

        // Collect any trailing comments.
        self.token();
        self.claim_gathered_comments(inst);

        Ok(())
    }

    // Type inference for polymorphic instructions.
    //
    // The controlling type variable can be specified explicitly as 'splat.i32x4 v5', or it can be
    // inferred from `inst_data.typevar_operand` for some opcodes.
    //
    // Returns the controlling typevar for a polymorphic opcode, or `VOID` for a non-polymorphic
    // opcode.
    fn infer_typevar(
        &self,
        ctx: &Context,
        opcode: Opcode,
        explicit_ctrl_type: Option<Type>,
        inst_data: &InstructionData,
    ) -> Result<Type> {
        let constraints = opcode.constraints();
        let ctrl_type = match explicit_ctrl_type {
            Some(t) => t,
            None => {
                if constraints.use_typevar_operand() {
                    // This is an opcode that supports type inference, AND there was no
                    // explicit type specified. Look up `ctrl_value` to see if it was defined
                    // already.
                    // TBD: If it is defined in another block, the type should have been
                    // specified explicitly. It is unfortunate that the correctness of IR
                    // depends on the layout of the blocks.
                    let ctrl_src_value = inst_data
                        .typevar_operand(&ctx.function.dfg.value_lists)
                        .expect("Constraints <-> Format inconsistency");
                    if !ctx.map.contains_value(ctrl_src_value) {
                        return err!(
                            self.loc,
                            "type variable required for polymorphic opcode, e.g. '{}.{}'; \
                             can't infer from {} which is not yet defined",
                            opcode,
                            constraints.ctrl_typeset().unwrap().example(),
                            ctrl_src_value
                        );
                    }
                    if !ctx.function.dfg.value_is_valid_for_parser(ctrl_src_value) {
                        return err!(
                            self.loc,
                            "type variable required for polymorphic opcode, e.g. '{}.{}'; \
                             can't infer from {} which is not yet resolved",
                            opcode,
                            constraints.ctrl_typeset().unwrap().example(),
                            ctrl_src_value
                        );
                    }
                    ctx.function.dfg.value_type(ctrl_src_value)
                } else if constraints.is_polymorphic() {
                    // This opcode does not support type inference, so the explicit type
                    // variable is required.
                    return err!(
                        self.loc,
                        "type variable required for polymorphic opcode, e.g. '{}.{}'",
                        opcode,
                        constraints.ctrl_typeset().unwrap().example()
                    );
                } else {
                    // This is a non-polymorphic opcode. No typevar needed.
                    VOID
                }
            }
        };

        // Verify that `ctrl_type` is valid for the controlling type variable. We don't want to
        // attempt deriving types from an incorrect basis.
        // This is not a complete type check. The verifier does that.
        if let Some(typeset) = constraints.ctrl_typeset() {
            // This is a polymorphic opcode.
            if !typeset.contains(ctrl_type) {
                return err!(
                    self.loc,
                    "{} is not a valid typevar for {}",
                    ctrl_type,
                    opcode
                );
            }
        // Treat it as a syntax error to speficy a typevar on a non-polymorphic opcode.
        } else if ctrl_type != VOID {
            return err!(self.loc, "{} does not take a typevar", opcode);
        }

        Ok(ctrl_type)
    }

    // Parse comma-separated value list into a VariableArgs struct.
    //
    // value_list ::= [ value { "," value } ]
    //
    fn parse_value_list(&mut self) -> Result<VariableArgs> {
        let mut args = VariableArgs::new();

        if let Some(Token::Value(v)) = self.token() {
            args.push(v);
            self.consume();
        } else {
            return Ok(args);
        }

        while self.optional(Token::Comma) {
            args.push(self.match_value("expected value in argument list")?);
        }

        Ok(args)
    }

    // Parse an optional value list enclosed in parantheses.
    fn parse_opt_value_list(&mut self) -> Result<VariableArgs> {
        if !self.optional(Token::LPar) {
            return Ok(VariableArgs::new());
        }

        let args = self.parse_value_list()?;

        self.match_token(
            Token::RPar,
            "expected ')' after arguments",
        )?;

        Ok(args)
    }

    // Parse the operands following the instruction opcode.
    // This depends on the format of the opcode.
    fn parse_inst_operands(
        &mut self,
        ctx: &mut Context,
        opcode: Opcode,
    ) -> Result<InstructionData> {
        let idata = match opcode.format() {
            InstructionFormat::Unary => InstructionData::Unary {
                opcode,
                arg: self.match_value("expected SSA value operand")?,
            },
            InstructionFormat::UnaryImm => InstructionData::UnaryImm {
                opcode,
                imm: self.match_imm64("expected immediate integer operand")?,
            },
            InstructionFormat::UnaryIeee32 => InstructionData::UnaryIeee32 {
                opcode,
                imm: self.match_ieee32("expected immediate 32-bit float operand")?,
            },
            InstructionFormat::UnaryIeee64 => InstructionData::UnaryIeee64 {
                opcode,
                imm: self.match_ieee64("expected immediate 64-bit float operand")?,
            },
            InstructionFormat::UnaryBool => InstructionData::UnaryBool {
                opcode,
                imm: self.match_bool("expected immediate boolean operand")?,
            },
            InstructionFormat::UnaryGlobalVar => {
                let gv = self.match_gv("expected global variable")?;
                ctx.check_gv(gv, &self.loc)?;
                InstructionData::UnaryGlobalVar {
                    opcode,
                    global_var: gv,
                }
            }
            InstructionFormat::Binary => {
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_value("expected SSA value second operand")?;
                InstructionData::Binary {
                    opcode,
                    args: [lhs, rhs],
                }
            }
            InstructionFormat::BinaryImm => {
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_imm64(
                    "expected immediate integer second operand",
                )?;
                InstructionData::BinaryImm {
                    opcode,
                    arg: lhs,
                    imm: rhs,
                }
            }
            InstructionFormat::Ternary => {
                // Names here refer to the `select` instruction.
                // This format is also use by `fma`.
                let ctrl_arg = self.match_value("expected SSA value control operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let true_arg = self.match_value("expected SSA value true operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let false_arg = self.match_value("expected SSA value false operand")?;
                InstructionData::Ternary {
                    opcode,
                    args: [ctrl_arg, true_arg, false_arg],
                }
            }
            InstructionFormat::MultiAry => {
                let args = self.parse_value_list()?;
                InstructionData::MultiAry {
                    opcode,
                    args: args.into_value_list(&[], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::NullAry => InstructionData::NullAry { opcode },
            InstructionFormat::Jump => {
                // Parse the destination EBB number.
                let ebb_num = self.match_ebb("expected jump destination EBB")?;
                let args = self.parse_opt_value_list()?;
                InstructionData::Jump {
                    opcode,
                    destination: ebb_num,
                    args: args.into_value_list(&[], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::Branch => {
                let ctrl_arg = self.match_value("expected SSA value control operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let ebb_num = self.match_ebb("expected branch destination EBB")?;
                let args = self.parse_opt_value_list()?;
                InstructionData::Branch {
                    opcode,
                    destination: ebb_num,
                    args: args.into_value_list(&[ctrl_arg], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::BranchInt => {
                let cond = self.match_enum("expected intcc condition code")?;
                let arg = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let ebb_num = self.match_ebb("expected branch destination EBB")?;
                let args = self.parse_opt_value_list()?;
                InstructionData::BranchInt {
                    opcode,
                    cond,
                    destination: ebb_num,
                    args: args.into_value_list(&[arg], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::BranchFloat => {
                let cond = self.match_enum("expected floatcc condition code")?;
                let arg = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let ebb_num = self.match_ebb("expected branch destination EBB")?;
                let args = self.parse_opt_value_list()?;
                InstructionData::BranchFloat {
                    opcode,
                    cond,
                    destination: ebb_num,
                    args: args.into_value_list(&[arg], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::BranchIcmp => {
                let cond = self.match_enum("expected intcc condition code")?;
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_value("expected SSA value second operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let ebb_num = self.match_ebb("expected branch destination EBB")?;
                let args = self.parse_opt_value_list()?;
                InstructionData::BranchIcmp {
                    opcode,
                    cond,
                    destination: ebb_num,
                    args: args.into_value_list(&[lhs, rhs], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::BranchTable => {
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let table = self.match_jt()?;
                ctx.check_jt(table, &self.loc)?;
                InstructionData::BranchTable { opcode, arg, table }
            }
            InstructionFormat::InsertLane => {
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let lane = self.match_uimm8("expected lane number")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_value("expected SSA value last operand")?;
                InstructionData::InsertLane {
                    opcode,
                    lane,
                    args: [lhs, rhs],
                }
            }
            InstructionFormat::ExtractLane => {
                let arg = self.match_value("expected SSA value last operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let lane = self.match_uimm8("expected lane number")?;
                InstructionData::ExtractLane { opcode, lane, arg }
            }
            InstructionFormat::IntCompare => {
                let cond = self.match_enum("expected intcc condition code")?;
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_value("expected SSA value second operand")?;
                InstructionData::IntCompare {
                    opcode,
                    cond,
                    args: [lhs, rhs],
                }
            }
            InstructionFormat::IntCompareImm => {
                let cond = self.match_enum("expected intcc condition code")?;
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_imm64("expected immediate second operand")?;
                InstructionData::IntCompareImm {
                    opcode,
                    cond,
                    arg: lhs,
                    imm: rhs,
                }
            }
            InstructionFormat::IntCond => {
                let cond = self.match_enum("expected intcc condition code")?;
                let arg = self.match_value("expected SSA value")?;
                InstructionData::IntCond { opcode, cond, arg }
            }
            InstructionFormat::FloatCompare => {
                let cond = self.match_enum("expected floatcc condition code")?;
                let lhs = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let rhs = self.match_value("expected SSA value second operand")?;
                InstructionData::FloatCompare {
                    opcode,
                    cond,
                    args: [lhs, rhs],
                }
            }
            InstructionFormat::FloatCond => {
                let cond = self.match_enum("expected floatcc condition code")?;
                let arg = self.match_value("expected SSA value")?;
                InstructionData::FloatCond { opcode, cond, arg }
            }
            InstructionFormat::IntSelect => {
                let cond = self.match_enum("expected intcc condition code")?;
                let guard = self.match_value("expected SSA value first operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let v_true = self.match_value("expected SSA value second operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let v_false = self.match_value("expected SSA value third operand")?;
                InstructionData::IntSelect {
                    opcode,
                    cond,
                    args: [guard, v_true, v_false],
                }
            }
            InstructionFormat::Call => {
                let func_ref = self.match_fn("expected function reference")?;
                ctx.check_fn(func_ref, &self.loc)?;
                self.match_token(
                    Token::LPar,
                    "expected '(' before arguments",
                )?;
                let args = self.parse_value_list()?;
                self.match_token(
                    Token::RPar,
                    "expected ')' after arguments",
                )?;
                InstructionData::Call {
                    opcode,
                    func_ref,
                    args: args.into_value_list(&[], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::CallIndirect => {
                let sig_ref = self.match_sig("expected signature reference")?;
                ctx.check_sig(sig_ref, &self.loc)?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let callee = self.match_value("expected SSA value callee operand")?;
                self.match_token(
                    Token::LPar,
                    "expected '(' before arguments",
                )?;
                let args = self.parse_value_list()?;
                self.match_token(
                    Token::RPar,
                    "expected ')' after arguments",
                )?;
                InstructionData::CallIndirect {
                    opcode,
                    sig_ref,
                    args: args.into_value_list(&[callee], &mut ctx.function.dfg.value_lists),
                }
            }
            InstructionFormat::FuncAddr => {
                let func_ref = self.match_fn("expected function reference")?;
                ctx.check_fn(func_ref, &self.loc)?;
                InstructionData::FuncAddr { opcode, func_ref }
            }
            InstructionFormat::StackLoad => {
                let ss = self.match_ss("expected stack slot number: ss«n»")?;
                ctx.check_ss(ss, &self.loc)?;
                let offset = self.optional_offset32()?;
                InstructionData::StackLoad {
                    opcode,
                    stack_slot: ss,
                    offset,
                }
            }
            InstructionFormat::StackStore => {
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let ss = self.match_ss("expected stack slot number: ss«n»")?;
                ctx.check_ss(ss, &self.loc)?;
                let offset = self.optional_offset32()?;
                InstructionData::StackStore {
                    opcode,
                    arg,
                    stack_slot: ss,
                    offset,
                }
            }
            InstructionFormat::HeapAddr => {
                let heap = self.match_heap("expected heap identifier")?;
                ctx.check_heap(heap, &self.loc)?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let arg = self.match_value("expected SSA value heap address")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let imm = self.match_uimm32("expected 32-bit integer size")?;
                InstructionData::HeapAddr {
                    opcode,
                    heap,
                    arg,
                    imm,
                }
            }
            InstructionFormat::Load => {
                let flags = self.optional_memflags();
                let addr = self.match_value("expected SSA value address")?;
                let offset = self.optional_offset32()?;
                InstructionData::Load {
                    opcode,
                    flags,
                    arg: addr,
                    offset,
                }
            }
            InstructionFormat::Store => {
                let flags = self.optional_memflags();
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let addr = self.match_value("expected SSA value address")?;
                let offset = self.optional_offset32()?;
                InstructionData::Store {
                    opcode,
                    flags,
                    args: [arg, addr],
                    offset,
                }
            }
            InstructionFormat::RegMove => {
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let src = self.match_regunit(ctx.unique_isa)?;
                self.match_token(
                    Token::Arrow,
                    "expected '->' between register units",
                )?;
                let dst = self.match_regunit(ctx.unique_isa)?;
                InstructionData::RegMove {
                    opcode,
                    arg,
                    src,
                    dst,
                }
            }
            InstructionFormat::CopySpecial => {
                let src = self.match_regunit(ctx.unique_isa)?;
                self.match_token(
                    Token::Arrow,
                    "expected '->' between register units",
                )?;
                let dst = self.match_regunit(ctx.unique_isa)?;
                InstructionData::CopySpecial { opcode, src, dst }
            }
            InstructionFormat::RegSpill => {
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let src = self.match_regunit(ctx.unique_isa)?;
                self.match_token(
                    Token::Arrow,
                    "expected '->' before destination stack slot",
                )?;
                let dst = self.match_ss("expected stack slot number: ss«n»")?;
                ctx.check_ss(dst, &self.loc)?;
                InstructionData::RegSpill {
                    opcode,
                    arg,
                    src,
                    dst,
                }
            }
            InstructionFormat::RegFill => {
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let src = self.match_ss("expected stack slot number: ss«n»")?;
                ctx.check_ss(src, &self.loc)?;
                self.match_token(
                    Token::Arrow,
                    "expected '->' before destination register units",
                )?;
                let dst = self.match_regunit(ctx.unique_isa)?;
                InstructionData::RegFill {
                    opcode,
                    arg,
                    src,
                    dst,
                }
            }
            InstructionFormat::Trap => {
                let code = self.match_enum("expected trap code")?;
                InstructionData::Trap { opcode, code }
            }
            InstructionFormat::CondTrap => {
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let code = self.match_enum("expected trap code")?;
                InstructionData::CondTrap { opcode, arg, code }
            }
            InstructionFormat::IntCondTrap => {
                let cond = self.match_enum("expected intcc condition code")?;
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let code = self.match_enum("expected trap code")?;
                InstructionData::IntCondTrap {
                    opcode,
                    cond,
                    arg,
                    code,
                }
            }
            InstructionFormat::FloatCondTrap => {
                let cond = self.match_enum("expected floatcc condition code")?;
                let arg = self.match_value("expected SSA value operand")?;
                self.match_token(
                    Token::Comma,
                    "expected ',' between operands",
                )?;
                let code = self.match_enum("expected trap code")?;
                InstructionData::FloatCondTrap {
                    opcode,
                    cond,
                    arg,
                    code,
                }
            }
        };
        Ok(idata)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cretonne_codegen::ir::StackSlotKind;
    use cretonne_codegen::ir::entities::AnyEntity;
    use cretonne_codegen::ir::types;
    use cretonne_codegen::ir::{ArgumentExtension, ArgumentPurpose};
    use cretonne_codegen::settings::CallConv;
    use error::Error;
    use isaspec::IsaSpec;
    use testfile::{Comment, Details};

    #[test]
    fn argument_type() {
        let mut p = Parser::new("i32 sext");
        let arg = p.parse_abi_param(None).unwrap();
        assert_eq!(arg.value_type, types::I32);
        assert_eq!(arg.extension, ArgumentExtension::Sext);
        assert_eq!(arg.purpose, ArgumentPurpose::Normal);
        let Error { location, message } = p.parse_abi_param(None).unwrap_err();
        assert_eq!(location.line_number, 1);
        assert_eq!(message, "expected parameter type");
    }

    #[test]
    fn aliases() {
        let (func, details) = Parser::new(
            "function %qux() system_v {
                                           ebb0:
                                             v4 = iconst.i8 6
                                             v3 -> v4
                                             v1 = iadd_imm v3, 17
                                           }",
        ).parse_function(None)
            .unwrap();
        assert_eq!(func.name.to_string(), "%qux");
        let v4 = details.map.lookup_str("v4").unwrap();
        assert_eq!(v4.to_string(), "v4");
        let v3 = details.map.lookup_str("v3").unwrap();
        assert_eq!(v3.to_string(), "v3");
        match v3 {
            AnyEntity::Value(v3) => {
                let aliased_to = func.dfg.resolve_aliases(v3);
                assert_eq!(aliased_to.to_string(), "v4");
            }
            _ => panic!("expected value: {}", v3),
        }
    }

    #[test]
    fn signature() {
        let sig = Parser::new("()system_v").parse_signature(None).unwrap();
        assert_eq!(sig.params.len(), 0);
        assert_eq!(sig.returns.len(), 0);
        assert_eq!(sig.call_conv, CallConv::SystemV);

        let sig2 = Parser::new("(i8 uext, f32, f64, i32 sret) -> i32 sext, f64 baldrdash")
            .parse_signature(None)
            .unwrap();
        assert_eq!(
            sig2.to_string(),
            "(i8 uext, f32, f64, i32 sret) -> i32 sext, f64 baldrdash"
        );
        assert_eq!(sig2.call_conv, CallConv::Baldrdash);

        // Old-style signature without a calling convention.
        assert_eq!(
            Parser::new("()").parse_signature(None).unwrap().to_string(),
            "() fast"
        );
        assert_eq!(
            Parser::new("() notacc")
                .parse_signature(None)
                .unwrap_err()
                .to_string(),
            "1: unknown calling convention: notacc"
        );

        // `void` is not recognized as a type by the lexer. It should not appear in files.
        assert_eq!(
            Parser::new("() -> void")
                .parse_signature(None)
                .unwrap_err()
                .to_string(),
            "1: expected parameter type"
        );
        assert_eq!(
            Parser::new("i8 -> i8")
                .parse_signature(None)
                .unwrap_err()
                .to_string(),
            "1: expected function signature: ( args... )"
        );
        assert_eq!(
            Parser::new("(i8 -> i8")
                .parse_signature(None)
                .unwrap_err()
                .to_string(),
            "1: expected ')' after function arguments"
        );
    }

    #[test]
    fn stack_slot_decl() {
        let (func, _) = Parser::new(
            "function %foo() system_v {
                                       ss3 = incoming_arg 13
                                       ss1 = spill_slot 1
                                     }",
        ).parse_function(None)
            .unwrap();
        assert_eq!(func.name.to_string(), "%foo");
        let mut iter = func.stack_slots.keys();
        let _ss0 = iter.next().unwrap();
        let ss1 = iter.next().unwrap();
        assert_eq!(ss1.to_string(), "ss1");
        assert_eq!(func.stack_slots[ss1].kind, StackSlotKind::SpillSlot);
        assert_eq!(func.stack_slots[ss1].size, 1);
        let _ss2 = iter.next().unwrap();
        let ss3 = iter.next().unwrap();
        assert_eq!(ss3.to_string(), "ss3");
        assert_eq!(func.stack_slots[ss3].kind, StackSlotKind::IncomingArg);
        assert_eq!(func.stack_slots[ss3].size, 13);
        assert_eq!(iter.next(), None);

        // Catch duplicate definitions.
        assert_eq!(
            Parser::new(
                "function %bar() system_v {
                                    ss1  = spill_slot 13
                                    ss1  = spill_slot 1
                                }",
            ).parse_function(None)
                .unwrap_err()
                .to_string(),
            "3: duplicate entity: ss1"
        );
    }

    #[test]
    fn ebb_header() {
        let (func, _) = Parser::new(
            "function %ebbs() system_v {
                                     ebb0:
                                     ebb4(v3: i32):
                                     }",
        ).parse_function(None)
            .unwrap();
        assert_eq!(func.name.to_string(), "%ebbs");

        let mut ebbs = func.layout.ebbs();

        let ebb0 = ebbs.next().unwrap();
        assert_eq!(func.dfg.ebb_params(ebb0), &[]);

        let ebb4 = ebbs.next().unwrap();
        let ebb4_args = func.dfg.ebb_params(ebb4);
        assert_eq!(ebb4_args.len(), 1);
        assert_eq!(func.dfg.value_type(ebb4_args[0]), types::I32);
    }

    #[test]
    fn comments() {
        let (func, Details { comments, .. }) = Parser::new(
            "; before
                         function %comment() system_v { ; decl
                            ss10  = outgoing_arg 13 ; stackslot.
                            ; Still stackslot.
                            jt10 = jump_table ebb0
                            ; Jumptable
                         ebb0: ; Basic block
                         trap user42; Instruction
                         } ; Trailing.
                         ; More trailing.",
        ).parse_function(None)
            .unwrap();
        assert_eq!(func.name.to_string(), "%comment");
        assert_eq!(comments.len(), 8); // no 'before' comment.
        assert_eq!(
            comments[0],
            Comment {
                entity: AnyEntity::Function,
                text: "; decl",
            }
        );
        assert_eq!(comments[1].entity.to_string(), "ss10");
        assert_eq!(comments[2].entity.to_string(), "ss10");
        assert_eq!(comments[2].text, "; Still stackslot.");
        assert_eq!(comments[3].entity.to_string(), "jt10");
        assert_eq!(comments[3].text, "; Jumptable");
        assert_eq!(comments[4].entity.to_string(), "ebb0");
        assert_eq!(comments[4].text, "; Basic block");

        assert_eq!(comments[5].entity.to_string(), "inst0");
        assert_eq!(comments[5].text, "; Instruction");

        assert_eq!(comments[6].entity, AnyEntity::Function);
        assert_eq!(comments[7].entity, AnyEntity::Function);
    }

    #[test]
    fn test_file() {
        let tf = parse_test(
            "; before
                             test cfg option=5
                             test verify
                             set enable_float=false
                             ; still preamble
                             function %comment() system_v {}",
        ).unwrap();
        assert_eq!(tf.commands.len(), 2);
        assert_eq!(tf.commands[0].command, "cfg");
        assert_eq!(tf.commands[1].command, "verify");
        match tf.isa_spec {
            IsaSpec::None(s) => {
                assert!(s.enable_verifier());
                assert!(!s.enable_float());
            }
            _ => panic!("unexpected ISAs"),
        }
        assert_eq!(tf.preamble_comments.len(), 2);
        assert_eq!(tf.preamble_comments[0].text, "; before");
        assert_eq!(tf.preamble_comments[1].text, "; still preamble");
        assert_eq!(tf.functions.len(), 1);
        assert_eq!(tf.functions[0].0.name.to_string(), "%comment");
    }

    #[test]
    #[cfg(build_riscv)]
    fn isa_spec() {
        assert!(
            parse_test(
                "isa
                            function %foo() system_v {}",
            ).is_err()
        );

        assert!(
            parse_test(
                "isa riscv
                            set enable_float=false
                            function %foo() system_v {}",
            ).is_err()
        );

        match parse_test(
            "set enable_float=false
                          isa riscv
                          function %foo() system_v {}",
        ).unwrap()
            .isa_spec {
            IsaSpec::None(_) => panic!("Expected some ISA"),
            IsaSpec::Some(v) => {
                assert_eq!(v.len(), 1);
                assert_eq!(v[0].name(), "riscv");
            }
        }
    }

    #[test]
    fn user_function_name() {
        // Valid characters in the name:
        let func = Parser::new(
            "function u1:2() system_v {
                                           ebb0:
                                             trap int_divz
                                           }",
        ).parse_function(None)
            .unwrap()
            .0;
        assert_eq!(func.name.to_string(), "u1:2");

        // Invalid characters in the name:
        let mut parser = Parser::new(
            "function u123:abc() system_v {
                                           ebb0:
                                             trap stk_ovf
                                           }",
        );
        assert!(parser.parse_function(None).is_err());

        // Incomplete function names should not be valid:
        let mut parser = Parser::new(
            "function u() system_v {
                                           ebb0:
                                             trap int_ovf
                                           }",
        );
        assert!(parser.parse_function(None).is_err());

        let mut parser = Parser::new(
            "function u0() system_v {
                                           ebb0:
                                             trap int_ovf
                                           }",
        );
        assert!(parser.parse_function(None).is_err());

        let mut parser = Parser::new(
            "function u0:() system_v {
                                           ebb0:
                                             trap int_ovf
                                           }",
        );
        assert!(parser.parse_function(None).is_err());
    }
}
