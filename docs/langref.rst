***************************
Cretonne Language Reference
***************************

.. default-domain:: cton
.. highlight:: cton

The Cretonne intermediate representation (:term:`IR`) has two primary forms:
an *in-memory data structure* that the code generator library is using, and a
*text format* which is used for test cases and debug output.
Files containing Cretonne textual IR have the ``.cton`` filename extension.

This reference uses the text format to describe IR semantics but glosses over
the finer details of the lexical and syntactic structure of the format.


Overall structure
=================

Cretonne compiles functions independently. A ``.cton`` IR file may contain
multiple functions, and the programmatic API can create multiple function
handles at the same time, but the functions don't share any data or reference
each other directly.

This is a simple C function that computes the average of an array of floats:

.. literalinclude:: example.c
    :language: c

Here is the same function compiled into Cretonne IR:

.. literalinclude:: example.cton
    :language: cton
    :lines: 2-

The first line of a function definition provides the function *name* and
the :term:`function signature` which declares the parameter and return types.
Then follows the :term:`function preamble` which declares a number of entities
that can be referenced inside the function. In the example above, the preamble
declares a single explicit stack slot, ``ss1``.

After the preamble follows the :term:`function body` which consists of
:term:`extended basic block`\s (EBBs), the first of which is the
:term:`entry block`. Every EBB ends with a :term:`terminator instruction`, so
execution can never fall through to the next EBB without an explicit branch.

A ``.cton`` file consists of a sequence of independent function definitions:

.. productionlist::
    function_list : { function }
    function      : "function" function_name signature "{" preamble function_body "}"
    preamble      : { preamble_decl }
    function_body : { extended_basic_block }

Static single assignment form
-----------------------------

The instructions in the function body use and produce *values* in SSA form. This
means that every value is defined exactly once, and every use of a value must be
dominated by the definition.

Cretonne does not have phi instructions but uses :term:`EBB parameter`\s
instead. An EBB can be defined with a list of typed parameters. Whenever control
is transferred to the EBB, argument values for the parameters must be provided.
When entering a function, the incoming function parameters are passed as
arguments to the entry EBB's parameters.

Instructions define zero, one, or more result values. All SSA values are either
EBB parameters or instruction results.

In the example above, the loop induction variable ``i`` is represented as three
SSA values: In the entry block, ``v4`` is the initial value. In the loop block
``ebb2``, the EBB parameter ``v5`` represents the value of the induction
variable during each iteration. Finally, ``v12`` is computed as the induction
variable value for the next iteration.

The `cretonne_frontend` crate contains utilities for translating from programs
containing multiple assignments to the same variables into SSA form for
Cretonne :term:`IR`.

Such variables can also be presented to Cretonne as :term:`stack slot`\s.
Stack slots are accessed with the :inst:`stack_store` and :inst:`stack_load`
instructions, and can have their address taken with :inst:`stack_addr`, which
supports C-like programming languages where local variables can have their
address taken.

.. _value-types:

Value types
===========

All SSA values have a type which determines the size and shape (for SIMD
vectors) of the value. Many instructions are polymorphic -- they can operate on
different types.

Boolean types
-------------

Boolean values are either true or false. While this only requires a single bit
to represent, more bits are often used when holding a boolean value in a
register or in memory. The :type:`b1` type represents an abstract boolean
value. It can only exist as an SSA value, it can't be stored in memory or
converted to another type. The larger boolean types can be stored in memory.
They are represented as either all zero bits or all one bits.

.. autoctontype:: b1
.. autoctontype:: b8
.. autoctontype:: b16
.. autoctontype:: b32
.. autoctontype:: b64

Integer types
-------------

Integer values have a fixed size and can be interpreted as either signed or
unsigned. Some instructions will interpret an operand as a signed or unsigned
number, others don't care.

.. autoctontype:: i8
.. autoctontype:: i16
.. autoctontype:: i32
.. autoctontype:: i64

Floating point types
--------------------

The floating point types have the IEEE 754 semantics that are supported by most
hardware, except that non-default rounding modes, unmasked exceptions, and
exception flags are not currently supported.

There is currently no support for higher-precision types like quad-precision,
double-double, or extended-precision, nor for narrower-precision types like
half-precision.

NaNs are encoded following the IEEE 754-2008 recommendation, with quiet NaN
being encoded with the MSB of the trailing significand set to 1, and signaling
NaNs being indicated by the MSB of the trailing significand set to 0.

Except for bitwise and memory instructions, NaNs returned from arithmetic
instructions are encoded as follows:

- If all NaN inputs to an instruction are quiet NaNs with all bits of the
  trailing significand other than the MSB set to 0, the result is a quiet
  NaN with a nondeterministic sign bit and all bits of the trailing
  significand other than the MSB set to 0.
- Otherwise the result is a quiet NaN with a nondeterministic sign bit
  and all bits of the trailing significand other than the MSB set to
  nondeterministic values.

.. autoctontype:: f32
.. autoctontype:: f64

CPU flags types
---------------

Some target ISAs use CPU flags to represent the result of a comparison. These
CPU flags are represented as two value types depending on the type of values
compared.

Since some ISAs don't have CPU flags, these value types should not be used
until the legalization phase of compilation where the code is adapted to fit
the target ISA. Use instructions like :inst:`icmp` instead.

The CPU flags types are also restricted such that two flags values can not be
live at the same time. After legalization, some instruction encodings will
clobber the flags, and flags values are not allowed to be live across such
instructions either. The verifier enforces these rules.

.. autoctontype:: iflags
.. autoctontype:: fflags

SIMD vector types
-----------------

A SIMD vector type represents a vector of values from one of the scalar types
(boolean, integer, and floating point). Each scalar value in a SIMD type is
called a *lane*. The number of lanes must be a power of two in the range 2-256.

.. type:: i%Bx%N

    A SIMD vector of integers. The lane type :type:`iB` is one of the integer
    types :type:`i8` ... :type:`i64`.

    Some concrete integer vector types are :type:`i32x4`, :type:`i64x8`, and
    :type:`i16x4`.

    The size of a SIMD integer vector in memory is :math:`N B\over 8` bytes.

.. type:: f32x%N

    A SIMD vector of single precision floating point numbers.

    Some concrete :type:`f32` vector types are: :type:`f32x2`, :type:`f32x4`,
    and :type:`f32x8`.

    The size of a :type:`f32` vector in memory is :math:`4N` bytes.

.. type:: f64x%N

    A SIMD vector of double precision floating point numbers.

    Some concrete :type:`f64` vector types are: :type:`f64x2`, :type:`f64x4`,
    and :type:`f64x8`.

    The size of a :type:`f64` vector in memory is :math:`8N` bytes.

.. type:: b1x%N

    A boolean SIMD vector.

    Boolean vectors are used when comparing SIMD vectors. For example,
    comparing two :type:`i32x4` values would produce a :type:`b1x4` result.

    Like the :type:`b1` type, a boolean vector cannot be stored in memory.

Pseudo-types and type classes
-----------------------------

These are not concrete types, but convenient names used to refer to real types
in this reference.

.. type:: iAddr

    A Pointer-sized integer representing an address.

    This is either :type:`i32`, or :type:`i64`, depending on whether the target
    platform has 32-bit or 64-bit pointers.

.. type:: iB

    Any of the scalar integer types :type:`i8` -- :type:`i64`.

.. type:: Int

    Any scalar *or vector* integer type: :type:`iB` or :type:`iBxN`.

.. type:: fB

    Either of the floating point scalar types: :type:`f32` or :type:`f64`.

.. type:: Float

    Any scalar *or vector* floating point type: :type:`fB` or :type:`fBxN`.

.. type:: %Tx%N

    Any SIMD vector type.

.. type:: Mem

    Any type that can be stored in memory: :type:`Int` or :type:`Float`.

.. type:: Testable

    Either :type:`b1` or :type:`iN`.

Immediate operand types
-----------------------

These types are not part of the normal SSA type system. They are used to
indicate the different kinds of immediate operands on an instruction.

.. type:: imm64

    A 64-bit immediate integer. The value of this operand is interpreted as a
    signed two's complement integer. Instruction encodings may limit the valid
    range.

    In the textual format, :type:`imm64` immediates appear as decimal or
    hexadecimal literals using the same syntax as C.

.. type:: offset32

    A signed 32-bit immediate address offset.

    In the textual format, :type:`offset32` immediates always have an explicit
    sign, and a 0 offset may be omitted.

.. type:: ieee32

    A 32-bit immediate floating point number in the IEEE 754-2008 binary32
    interchange format. All bit patterns are allowed.

.. type:: ieee64

    A 64-bit immediate floating point number in the IEEE 754-2008 binary64
    interchange format. All bit patterns are allowed.

.. type:: bool

    A boolean immediate value, either false or true.

    In the textual format, :type:`bool` immediates appear as 'false'
    and 'true'.

.. type:: intcc

    An integer condition code. See the :inst:`icmp` instruction for details.

.. type:: floatcc

    A floating point condition code. See the :inst:`fcmp` instruction for details.

The two IEEE floating point immediate types :type:`ieee32` and :type:`ieee64`
are displayed as hexadecimal floating point literals in the textual :term:`IR`
format. Decimal floating point literals are not allowed because some computer
systems can round differently when converting to binary. The hexadecimal
floating point format is mostly the same as the one used by C99, but extended
to represent all NaN bit patterns:

Normal numbers
    Compatible with C99: ``-0x1.Tpe`` where ``T`` are the trailing
    significand bits encoded as hexadecimal, and ``e`` is the unbiased exponent
    as a decimal number. :type:`ieee32` has 23 trailing significand bits. They
    are padded with an extra LSB to produce 6 hexadecimal digits. This is not
    necessary for :type:`ieee64` which has 52 trailing significand bits
    forming 13 hexadecimal digits with no padding.

Zeros
    Positive and negative zero are displayed as ``0.0`` and ``-0.0`` respectively.

Subnormal numbers
    Compatible with C99: ``-0x0.Tpemin`` where ``T`` are the trailing
    significand bits encoded as hexadecimal, and ``emin`` is the minimum exponent
    as a decimal number.

Infinities
    Either ``-Inf`` or ``Inf``.

Quiet NaNs
    Quiet NaNs have the MSB of the trailing significand set. If the remaining
    bits of the trailing significand are all zero, the value is displayed as
    ``-NaN`` or ``NaN``. Otherwise, ``-NaN:0xT`` where ``T`` are the trailing
    significand bits encoded as hexadecimal.

Signaling NaNs
    Displayed as ``-sNaN:0xT``.


Control flow
============

Branches transfer control to a new EBB and provide values for the target EBB's
arguments, if it has any. Conditional branches only take the branch if their
condition is satisfied, otherwise execution continues at the following
instruction in the EBB.

.. autoinst:: jump
.. autoinst:: fallthrough
.. autoinst:: brz
.. autoinst:: brnz
.. autoinst:: br_icmp
.. autoinst:: brif
.. autoinst:: brff
.. autoinst:: br_table

.. inst:: JT = jump_table EBB0, EBB1, ..., EBBn

    Declare a jump table in the :term:`function preamble`.

    This declares a jump table for use by the :inst:`br_table` indirect branch
    instruction. Entries in the table are either EBB names, or ``0`` which
    indicates an absent entry.

    The EBBs listed must belong to the current function, and they can't have
    any arguments.

    :arg EBB0: Target EBB when ``x = 0``.
    :arg EBB1: Target EBB when ``x = 1``.
    :arg EBBn: Target EBB when ``x = n``.
    :result: A jump table identifier. (Not an SSA value).

Traps stop the program because something went wrong. The exact behavior depends
on the target instruction set architecture and operating system. There are
explicit trap instructions defined below, but some instructions may also cause
traps for certain input value. For example, :inst:`udiv` traps when the divisor
is zero.

.. autoinst:: trap
.. autoinst:: trapz
.. autoinst:: trapnz
.. autoinst:: trapif
.. autoinst:: trapff


Function calls
==============

A function call needs a target function and a :term:`function signature`. The
target function may be determined dynamically at runtime, but the signature must
be known when the function call is compiled. The function signature describes
how to call the function, including parameters, return values, and the calling
convention:

.. productionlist::
    signature    : "(" [paramlist] ")" ["->" retlist] [call_conv]
    paramlist    : param { "," param }
    retlist      : paramlist
    param        : type [paramext] [paramspecial]
    paramext     : "uext" | "sext"
    paramspecial : "sret" | "link" | "fp" | "csr" | "vmctx"
    callconv     : "fast" | "cold" | "system_v" | "fastcall" | "baldrdash"

A function's calling convention determines exactly how arguments and return
values are passed, and how stack frames are managed. Since all of these details
depend on both the instruction set /// architecture and possibly the operating
system, a function's calling convention is only fully determined by a
`(TargetIsa, CallConv)` tuple.

========== ===========================================
Name       Description
========== ===========================================
fast       not-ABI-stable convention for best performance
cold       not-ABI-stable convention for infrequently executed code
system_v   System V-style convention used on many platforms
fastcall   Windows "fastcall" convention, also used for x64 and ARM
baldrdash  SpiderMonkey WebAssembly convention
========== ===========================================

The "not-ABI-stable" conventions do not follow an external specification and
may change between versions of Cretonne.

The "fastcall" convention is not yet implemented.

Parameters and return values have flags whose meaning is mostly target
dependent. These flags support interfacing with code produced by other
compilers.

Functions that are called directly must be declared in the :term:`function
preamble`:

.. inst:: FN = [colocated] NAME signature

    Declare a function so it can be called directly.

    If the colocated keyword is present, the symbol's definition will be
    defined along with the current function, such that it can use more
    efficient addressing.

    :arg NAME: Name of the function, passed to the linker for resolution.
    :arg signature: Function signature. See below.
    :result FN: A function identifier that can be used with :inst:`call`.

.. autoinst:: call
.. autoinst:: x_return

This simple example illustrates direct function calls and signatures:

.. literalinclude:: callex.cton
    :language: cton
    :lines: 3-

Indirect function calls use a signature declared in the preamble.

.. autoinst:: call_indirect
.. autoinst:: func_addr

.. _memory:

Memory
======

Cretonne provides fully general :inst:`load` and :inst:`store` instructions for
accessing memory, as well as :ref:`extending loads and truncating stores
<extload-truncstore>`.

If the memory at the given address is not :term:`addressable`, the behavior of
these instructions is undefined. If it is addressable but not
:term:`accessible`, they :term:`trap`.

.. autoinst:: load
.. autoinst:: store

There are also more restricted operations for accessing specific types of memory
objects.

Memory operation flags
----------------------

Loads and stores can have flags that loosen their semantics in order to enable
optimizations.

======= ===========================================
Flag    Description
======= ===========================================
notrap  Memory is assumed to be :term:`accessible`.
aligned Trapping allowed for misaligned accesses.
======= ===========================================

When the ``accessible`` flag is set, the behavior is undefined if the memory
is not :term:`accessible`.

Loads and stores are *misaligned* if the resultant address is not a multiple of
the expected alignment. By default, misaligned loads and stores are allowed,
but when the ``aligned`` flag is set, a misaligned memory access is allowed to
:term:`trap`.

Explicit Stack Slots
--------------------

One set of restricted memory operations access the current function's stack
frame. The stack frame is divided into fixed-size stack slots that are
allocated in the :term:`function preamble`. Stack slots are not typed, they
simply represent a contiguous sequence of :term:`accessible` bytes in the stack
frame.

.. inst:: SS = explicit_slot Bytes, Flags...

    Allocate a stack slot in the preamble.

    If no alignment is specified, Cretonne will pick an appropriate alignment
    for the stack slot based on its size and access patterns.

    :arg Bytes: Stack slot size on bytes.
    :flag align(N): Request at least N bytes alignment.
    :result SS: Stack slot index.

.. autoinst:: stack_load
.. autoinst:: stack_store

The dedicated stack access instructions are easy for the compiler to reason
about because stack slots and offsets are fixed at compile time. For example,
the alignment of these stack memory accesses can be inferred from the offsets
and stack slot alignments.

It's also possible to obtain the address of a stack slot, which can be used
in :ref:`unrestricted loads and stores <memory>`.

.. autoinst:: stack_addr

The :inst:`stack_addr` instruction can be used to macro-expand the stack access
instructions before instruction selection::

    v1 = stack_load.f64 ss3, 16
    ; Expands to:
    v9 = stack_addr ss3, 16
    v1 = load.f64 v9

When Cretonne code is running in a sandbox, it can also be necessary to include
stack overflow checks in the prologue.

.. autoinst:: stack_check

Global variables
----------------

A *global variable* is an :term:`accessible` object in memory whose address is
not known at compile time. The address is computed at runtime by
:inst:`global_addr`, possibly using information provided by the linker via
relocations. There are multiple kinds of global variables using different
methods for determining their address. Cretonne does not track the type or even
the size of global variables, they are just pointers to non-stack memory.

When Cretonne is generating code for a virtual machine environment, globals can
be used to access data structures in the VM's runtime. This requires functions
to have access to a *VM context pointer* which is used as the base address.
Typically, the VM context pointer is passed as a hidden function argument to
Cretonne functions.

.. inst:: GV = vmctx+Offset

    Declare a global variable in the VM context struct.

    This declares a global variable whose address is a constant offset from the
    VM context pointer which is passed as a hidden argument to all functions
    JIT-compiled for the VM.

    Typically, the VM context is a C struct, and the declared global variable
    is a member of the struct.

    :arg Offset: Byte offset from the VM context pointer to the global
                 variable.
    :result GV: Global variable.

The address of a global variable can also be derived by treating another global
variable as a struct pointer. This makes it possible to chase pointers into VM
runtime data structures.

.. inst:: GV = deref(BaseGV)+Offset

    Declare a global variable in a struct pointed to by BaseGV.

    The address of GV can be computed by first loading a pointer from BaseGV
    and adding Offset to it.

    It is assumed the BaseGV resides in readable memory with the appropriate
    alignment for storing a pointer.

    Chains of ``deref`` global variables are possible, but cycles are not
    allowed. They will be caught by the IR verifier.

    :arg BaseGV: Global variable containing the base pointer.
    :arg Offset: Byte offset from the loaded base pointer to the global
                 variable.
    :result GV: Global variable.

.. inst:: GV = [colocated] globalsym name

    Declare a global variable at a symbolic address.

    The address of GV is symbolic and will be assigned a relocation, so that
    it can be resolved by a later linking phase.

    If the colocated keyword is present, the symbol's definition will be
    defined along with the current function, such that it can use more
    efficient addressing.

    :arg name: External name.
    :result GV: Global variable.

.. autoinst:: global_addr
.. autoinst:: globalsym_addr


Heaps
-----

Code compiled from WebAssembly or asm.js runs in a sandbox where it can't access
all process memory. Instead, it is given a small set of memory areas to work
in, and all accesses are bounds checked. Cretonne models this through the
concept of *heaps*.

A heap is declared in the function preamble and can be accessed with the
:inst:`heap_addr` instruction that :term:`traps` on out-of-bounds accesses or
returns a pointer that is guaranteed to trap. Heap addresses can be smaller than
the native pointer size, for example unsigned :type:`i32` offsets on a 64-bit
architecture.

.. digraph:: static
    :align: center
    :caption: Heap address space layout

    node [
        shape=record,
        fontsize=10,
        fontname="Vera Sans, DejaVu Sans, Liberation Sans, Arial, Helvetica, sans"
    ]
    "static" [label="mapped\npages|unmapped\npages|guard\npages"]

A heap appears as three consecutive ranges of address space:

1. The *mapped pages* are the :term:`accessible` memory range in the heap. A
   heap may have a minimum guaranteed size which means that some mapped pages
   are always present.
2. The *unmapped pages* is a possibly empty range of address space that may be
   mapped in the future when the heap is grown. They are :term:`addressable` but
   not :term:`accessible`.
3. The *guard pages* is a range of address space that is guaranteed to cause a
   trap when accessed. It is used to optimize bounds checking for heap accesses
   with a shared base pointer. They are :term:`addressable` but
   not :term:`accessible`.

The *heap bound* is the total size of the mapped and unmapped pages. This is
the bound that :inst:`heap_addr` checks against. Memory accesses inside the
heap bounds can trap if they hit an unmapped page (which is not
:term:`accessible`).

.. autoinst:: heap_addr

Two styles of heaps are supported, *static* and *dynamic*. They behave
differently when resized.

Static heaps
~~~~~~~~~~~~

A *static heap* starts out with all the address space it will ever need, so it
never moves to a different address. At the base address is a number of mapped
pages corresponding to the heap's current size. Then follows a number of
unmapped pages where the heap can grow up to its maximum size. After the
unmapped pages follow the guard pages which are also guaranteed to generate a
trap when accessed.

.. inst:: H = static Base, min MinBytes, bound BoundBytes, guard GuardBytes

    Declare a static heap in the preamble.

    :arg Base: Global variable holding the heap's base address or
            ``reserved_reg``.
    :arg MinBytes: Guaranteed minimum heap size in bytes. Accesses below this
            size will never trap.
    :arg BoundBytes: Fixed heap bound in bytes. This defines the amount of
            address space reserved for the heap, not including the guard pages.
    :arg GuardBytes: Size of the guard pages in bytes.

When the base is a global variable, it must be :term:`accessible` and naturally
aligned for a pointer value.

The ``reserved_reg`` option is not yet implemented.

Dynamic heaps
~~~~~~~~~~~~~

A *dynamic heap* can be relocated to a different base address when it is
resized, and its bound can move dynamically. The guard pages move when the heap
is resized. The bound of a dynamic heap is stored in a global variable.

.. inst:: H = dynamic Base, min MinBytes, bound BoundGV, guard GuardBytes

    Declare a dynamic heap in the preamble.

    :arg Base: Global variable holding the heap's base address or
            ``reserved_reg``.
    :arg MinBytes: Guaranteed minimum heap size in bytes. Accesses below this
            size will never trap.
    :arg BoundGV: Global variable containing the current heap bound in bytes.
    :arg GuardBytes: Size of the guard pages in bytes.

When the base is a global variable, it must be :term:`accessible` and naturally
aligned for a pointer value.

The ``reserved_reg`` option is not yet implemented.

Heap examples
~~~~~~~~~~~~~

The SpiderMonkey VM prefers to use fixed heaps with a 4 GB bound and 2 GB of
guard pages when running WebAssembly code on 64-bit CPUs. The combination of a
4 GB fixed bound and 1-byte bounds checks means that no code needs to be
generated for bounds checks at all:

.. literalinclude:: heapex-sm64.cton
    :language: cton
    :lines: 2-

A static heap can also be used for 32-bit code when the WebAssembly module
declares a small upper bound on its memory. A 1 MB static bound with a single 4
KB guard page still has opportunities for sharing bounds checking code:

.. literalinclude:: heapex-sm32.cton
    :language: cton
    :lines: 2-

If the upper bound on the heap size is too large, a dynamic heap is required
instead.

Finally, a runtime environment that simply allocates a heap with
:c:func:`malloc()` may not have any guard pages at all. In that case, full
bounds checking is required for each access:

.. literalinclude:: heapex-dyn.cton
    :language: cton
    :lines: 2-


Operations
==========

.. autoinst:: select
.. autoinst:: selectif

Constant materialization
------------------------

A few instructions have variants that take immediate operands (e.g.,
:inst:`band` / :inst:`band_imm`), but in general an instruction is required to
load a constant into an SSA value.

.. autoinst:: iconst
.. autoinst:: f32const
.. autoinst:: f64const
.. autoinst:: bconst

Live range splitting
--------------------

Cretonne's register allocator assigns each SSA value to a register or a spill
slot on the stack for its entire live range. Since the live range of an SSA
value can be quite large, it is sometimes beneficial to split the live range
into smaller parts.

A live range is split by creating new SSA values that are copies or the
original value or each other. The copies are created by inserting :inst:`copy`,
:inst:`spill`, or :inst:`fill` instructions, depending on whether the values
are assigned to registers or stack slots.

This approach permits SSA form to be preserved throughout the register
allocation pass and beyond.

.. autoinst:: copy
.. autoinst:: spill
.. autoinst:: fill

Register values can be temporarily diverted to other registers by the
:inst:`regmove` instruction, and to and from stack slots by :inst:`regspill`
and :inst:`regfill`.

.. autoinst:: regmove
.. autoinst:: regspill
.. autoinst:: regfill

Vector operations
-----------------

.. autoinst:: vsplit
.. autoinst:: vconcat
.. autoinst:: vselect
.. autoinst:: splat
.. autoinst:: insertlane
.. autoinst:: extractlane

Integer operations
------------------

.. autoinst:: icmp
.. autoinst:: icmp_imm
.. autoinst:: ifcmp
.. autoinst:: ifcmp_imm
.. autoinst:: iadd
.. autoinst:: iadd_imm
.. autoinst:: iadd_cin
.. autoinst:: iadd_cout
.. autoinst:: iadd_carry
.. autoinst:: isub
.. autoinst:: irsub_imm
.. autoinst:: isub_bin
.. autoinst:: isub_bout
.. autoinst:: isub_borrow

.. todo:: Add and subtract with signed overflow.

    For example, see
    `llvm.sadd.with.overflow.*` and `llvm.ssub.with.overflow.*` in
    `LLVM <https://llvm.org/docs/LangRef.html#arithmetic-with-overflow-intrinsics>`_.

.. autoinst:: imul
.. autoinst:: imul_imm

.. todo:: Larger multiplication results.

    For example, ``smulx`` which multiplies :type:`i32` operands to produce a
    :type:`i64` result. Alternatively, ``smulhi`` and ``smullo`` pairs.

.. autoinst:: udiv
.. autoinst:: udiv_imm
.. autoinst:: sdiv
.. autoinst:: sdiv_imm
.. autoinst:: urem
.. autoinst:: urem_imm
.. autoinst:: srem
.. autoinst:: srem_imm

.. todo:: Integer minimum / maximum.

    NEON has ``smin``, ``smax``, ``umin``, and ``umax`` instructions. We should
    replicate those for both scalar and vector integer types. Even if the
    target ISA doesn't have scalar operations, these are good pattern matching
    targets.

.. todo:: Saturating arithmetic.

    Mostly for SIMD use, but again these are good patterns for contraction.
    Something like ``usatadd``, ``usatsub``, ``ssatadd``, and ``ssatsub`` is a
    good start.

Bitwise operations
------------------

The bitwise operations and operate on any value type: Integers, floating point
numbers, and booleans. When operating on integer or floating point types, the
bitwise operations are working on the binary representation of the values. When
operating on boolean values, the bitwise operations work as logical operators.

.. autoinst:: band
.. autoinst:: band_imm
.. autoinst:: bor
.. autoinst:: bor_imm
.. autoinst:: bxor
.. autoinst:: bxor_imm
.. autoinst:: bnot
.. autoinst:: band_not
.. autoinst:: bor_not
.. autoinst:: bxor_not

The shift and rotate operations only work on integer types (scalar and vector).
The shift amount does not have to be the same type as the value being shifted.
Only the low `B` bits of the shift amount is significant.

When operating on an integer vector type, the shift amount is still a scalar
type, and all the lanes are shifted the same amount. The shift amount is masked
to the number of bits in a *lane*, not the full size of the vector type.

.. autoinst:: rotl
.. autoinst:: rotl_imm
.. autoinst:: rotr
.. autoinst:: rotr_imm
.. autoinst:: ishl
.. autoinst:: ishl_imm
.. autoinst:: ushr
.. autoinst:: ushr_imm
.. autoinst:: sshr
.. autoinst:: sshr_imm

The bit-counting instructions below are scalar only.

.. autoinst:: clz
.. autoinst:: cls
.. autoinst:: ctz
.. autoinst:: popcnt

Floating point operations
-------------------------

These operations generally follow IEEE 754-2008 semantics.

.. autoinst:: fcmp
.. autoinst:: ffcmp
.. autoinst:: fadd
.. autoinst:: fsub
.. autoinst:: fmul
.. autoinst:: fdiv
.. autoinst:: sqrt
.. autoinst:: fma

Sign bit manipulations
~~~~~~~~~~~~~~~~~~~~~~

The sign manipulating instructions work as bitwise operations, so they don't
have special behavior for signaling NaN operands. The exponent and trailing
significand bits are always preserved.

.. autoinst:: fneg
.. autoinst:: fabs
.. autoinst:: fcopysign

Minimum and maximum
~~~~~~~~~~~~~~~~~~~

These instructions return the larger or smaller of their operands. Note that
unlike the IEEE 754-2008 `minNum` and `maxNum` operations, these instructions
return NaN when either input is NaN.

When comparing zeroes, these instructions behave as if :math:`-0.0 < 0.0`.

.. autoinst:: fmin
.. autoinst:: fmax

Rounding
~~~~~~~~

These instructions round their argument to a nearby integral value, still
represented as a floating point number.

.. autoinst:: ceil
.. autoinst:: floor
.. autoinst:: trunc
.. autoinst:: nearest

CPU flag operations
-------------------

.. autoinst:: trueif
.. autoinst:: trueff

Conversion operations
---------------------

.. autoinst:: bitcast
.. autoinst:: breduce
.. autoinst:: bextend
.. autoinst:: bint
.. autoinst:: bmask
.. autoinst:: ireduce
.. autoinst:: uextend
.. autoinst:: sextend
.. autoinst:: fpromote
.. autoinst:: fdemote
.. autoinst:: fcvt_to_uint
.. autoinst:: fcvt_to_sint
.. autoinst:: fcvt_from_uint
.. autoinst:: fcvt_from_sint

.. todo:: Saturating fcvt_to_sint and fcvt_to_uint.

    For example, these appear in
    `Rust <https://github.com/rust-lang/rust/pull/45205>`_ and
    `WebAssembly <https://github.com/WebAssembly/nontrapping-float-to-int-conversions>`_.

Legalization operations
-----------------------

These instructions are used as helpers when legalizing types and operations for
the target ISA.

.. autoinst:: isplit
.. autoinst:: iconcat

Special register operations
---------------------------

The prologue and epilogue of a function needs to manipulate special registers like the stack
pointer and the frame pointer. These instructions should not be used in regular code.

.. autoinst:: adjust_sp_imm
.. autoinst:: ifcmp_sp
.. autoinst:: copy_special

.. _extload-truncstore:

Extending loads and truncating stores
-------------------------------------

Most ISAs provide instructions that load an integer value smaller than a register
and extends it to the width of the register. Similarly, store instructions that
only write the low bits of an integer register are common.

In addition to the normal :inst:`load` and :inst:`store` instructions, Cretonne
provides extending loads and truncation stores for 8, 16, and 32-bit memory
accesses.

These instructions succeed, trap, or have undefined behavior, under the same
conditions as :ref:`normal loads and stores <memory>`.

.. autoinst:: uload8
.. autoinst:: sload8
.. autoinst:: istore8
.. autoinst:: uload16
.. autoinst:: sload16
.. autoinst:: istore16
.. autoinst:: uload32
.. autoinst:: sload32
.. autoinst:: istore32

ISA-specific instructions
=========================

Target ISAs can define supplemental instructions that do not make sense to
support generally.

x86
-----

Instructions that can only be used by the x86 target ISA.

.. autoinst:: isa.x86.instructions.sdivmodx
.. autoinst:: isa.x86.instructions.udivmodx
.. autoinst:: isa.x86.instructions.cvtt2si
.. autoinst:: isa.x86.instructions.fmin
.. autoinst:: isa.x86.instructions.fmax
.. autoinst:: isa.x86.instructions.bsf
.. autoinst:: isa.x86.instructions.bsr
.. autoinst:: isa.x86.instructions.push
.. autoinst:: isa.x86.instructions.pop

Instruction groups
==================

All of the shared instructions are part of the :instgroup:`base` instruction
group.

.. autoinstgroup:: base.instructions.GROUP

Target ISAs may define further instructions in their own instruction groups:

.. autoinstgroup:: isa.x86.instructions.GROUP

Implementation limits
=====================

Cretonne's intermediate representation imposes some limits on the size of
functions and the number of entities allowed. If these limits are exceeded, the
implementation will panic.

Number of instructions in a function
    At most :math:`2^{31} - 1`.

Number of EBBs in a function
    At most :math:`2^{31} - 1`.

    Every EBB needs at least a terminator instruction anyway.

Number of secondary values in a function
    At most :math:`2^{31} - 1`.

    Secondary values are any SSA values that are not the first result of an
    instruction.

Other entities declared in the preamble
    At most :math:`2^{32} - 1`.

    This covers things like stack slots, jump tables, external functions, and
    function signatures, etc.

Number of arguments to an EBB
    At most :math:`2^{16}`.

Number of arguments to a function
    At most :math:`2^{16}`.

    This follows from the limit on arguments to the entry EBB. Note that
    Cretonne may add a handful of ABI register arguments as function signatures
    are lowered. This is for representing things like the link register, the
    incoming frame pointer, and callee-saved registers that are saved in the
    prologue.

Size of function call arguments on the stack
    At most :math:`2^{32} - 1` bytes.

    This is probably not possible to achieve given the limit on the number of
    arguments, except by requiring extremely large offsets for stack arguments.

Glossary
========

.. glossary::

    addressable
        Memory in which loads and stores have defined behavior. They either
        succeed or :term:`trap`, depending on whether the memory is
        :term:`accessible`.

    accessible
        :term:`Addressable` memory in which loads and stores always succeed
        without :term:`trapping`, except where specified otherwise (eg. with the
        `aligned` flag). Heaps, globals, and the stack may contain accessible,
        merely addressable, and outright unaddressable regions. There may also
        be additional regions of addressable and/or accessible memory not
        explicitly declared.

    basic block
        A maximal sequence of instructions that can only be entered from the
        top, and that contains no branch or terminator instructions except for
        the last instruction.

    entry block
        The :term:`EBB` that is executed first in a function. Currently, a
        Cretonne function must have exactly one entry block which must be the
        first block in the function. The types of the entry block arguments must
        match the types of arguments in the function signature.

    extended basic block
    EBB
        A maximal sequence of instructions that can only be entered from the
        top, and that contains no :term:`terminator instruction`\s except for
        the last one. An EBB can contain conditional branches that can fall
        through to the following instructions in the block, but only the first
        instruction in the EBB can be a branch target.

        The last instruction in an EBB must be a :term:`terminator instruction`,
        so execution cannot flow through to the next EBB in the function. (But
        there may be a branch to the next EBB.)

        Note that some textbooks define an EBB as a maximal *subtree* in the
        control flow graph where only the root can be a join node. This
        definition is not equivalent to Cretonne EBBs.

    EBB parameter
        A formal parameter for an EBB is an SSA value that dominates everything
        in the EBB. For each parameter declared by an EBB, a corresponding
        argument value must be passed when branching to the EBB. The function's
        entry EBB has parameters that correspond to the function's parameters.

    EBB argument
        Similar to function arguments, EBB arguments must be provided when
        branching to an EBB that declares formal parameters. When execution
        begins at the top of an EBB, the formal parameters have the values of
        the arguments passed in the branch.

    function signature
        A function signature describes how to call a function. It consists of:

        - The calling convention.
        - The number of arguments and return values. (Functions can return
          multiple values.)
        - Type and flags of each argument.
        - Type and flags of each return value.

        Not all function attributes are part of the signature. For example, a
        function that never returns could be marked as ``noreturn``, but that
        is not necessary to know when calling it, so it is just an attribute,
        and not part of the signature.

    function preamble
        A list of declarations of entities that are used by the function body.
        Some of the entities that can be declared in the preamble are:

        - Stack slots.
        - Functions that are called directly.
        - Function signatures for indirect function calls.
        - Function flags and attributes that are not part of the signature.

    function body
        The extended basic blocks which contain all the executable code in a
        function. The function body follows the function preamble.

    intermediate representation
    IR
        The language used to describe functions to Cretonne. This reference
        describes the syntax and semantics of Cretonne IR. The IR has two
        forms: Textual, and an in-memory data structure.

    stack slot
        A fixed size memory allocation in the current function's activation
        frame. These include :term:`explicit stack slot`\s and
        :term:`spill stack slot`\s.

    explicit stack slot
        A fixed size memory allocation in the current function's activation
        frame. These differ from :term:`spill stack slot`\s in that they can
        be created by frontends and they may have their addresses taken.

    spill stack slot
        A fixed size memory allocation in the current function's activation
        frame. These differ from :term:`explicit stack slot`\s in that they are
        only created during register allocation, and they may not have their
        address taken.

    terminator instruction
        A control flow instruction that unconditionally directs the flow of
        execution somewhere else. Execution never continues at the instruction
        following a terminator instruction.

        The basic terminator instructions are :inst:`br`, :inst:`return`, and
        :inst:`trap`. Conditional branches and instructions that trap
        conditionally are not terminator instructions.

    trap
    traps
    trapping
        Terminates execution of the current thread. The specific behavior after
        a trap depends on the underlying OS. For example, a common behavior is
        delivery of a signal, with the specific signal depending on the event
        that triggered it.
