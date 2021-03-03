/*a Copyright

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

  http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@file    picoinstruction.rs
@brief   Picoinstructio
 */

//a Imports

//a Constants
//pc Const
//a Instruction opcodes etc
//tp ArithOp
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum ArithOp {
 Neg  = 0,
 Add  = 1,
 Sub  = 2,
 Mul  = 3,
 Div  = 4,
 Mod  = 5,
}

//ip ArithOp
impl ArithOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Self {
        num::FromPrimitive::from_usize(n).unwrap()
    }
}

//tp LogicOp
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum LogicOp {
 BoolNot = 0,
 And  = 1,
 Or   = 2,
 Xor  = 3,
 Lsl  = 4,
 Lsr  = 5,
 Asr  = 6,
}
//ip LogicOp
impl LogicOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Self {
        num::FromPrimitive::from_usize(n).unwrap()
    }
}

//tp CmpOp
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum CmpOp {
 Eq   = 0,
 Ne   = 1,
 Lt   = 2,
 Le   = 3,
 Gt   = 4,
 Ge   = 5,
 Ult  = 6,
 Uge  = 7,
}

//ip CmpOp
impl CmpOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Self {
        num::FromPrimitive::from_usize(n).unwrap()
    }
}

//tp BranchOp
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum BranchOp {
 Eq   = 0,
 Ne   = 1,
 Al   = 2,
}

//ip BranchOp
impl BranchOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Self {
        num::FromPrimitive::from_usize(n).unwrap()
    }
}

//tp Opcode
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum Opcode {
    /// accumulator OP stack.pop() -- which OP is subop
    ArithOp           = 0x00, // immediate value is type of int operation
    /// accumulator OP stack.pop() -- which OP is subop
    LogicOp           = 0x01, // immediate value is type of int operation
    /// accumulator CMP stack.pop() -- which OP is subop
    IntCmp            = 0x02, // N => eq, ne, lt, le, gt, ge, ult, uge,
    /// accumulator CMP stack.pop() -- which OP is subop - and branch by arg1
    IntBranch         = 0x03, // N => eq, ne, lt, le, gt, ge, ult, uge - REQUIRES arg1
    /// Set accumulator to a constant integer value from code or immediate
    Const             = 0x04,
    /// Push accumulator the set accumulator to a constant
    PushConst         = 0x05,
    /// Set accumulator to the stack at an offset
    Acc               = 0x06,
    /// Push accumulator the set accumulator to the stack at an offset
    PushAcc           = 0x07,
    /// Set accumulator to the Nth environment field
    EnvAcc            = 0x08,
    /// Push accumulator the set accumulator to the Nth environment field
    PushEnvAcc        = 0x09,
    /// Set accumulator to the Nth environment field
    OffsetClosure     = 0x0a,
    /// Push accumulator the set accumulator to the Nth environment field
    PushOffsetClosure = 0x0b,
    /// Pop N, from an immediate or next code
    Pop               = 0x0c,
    /// Assign stack[offset] to the accumulatore
    Assign            = 0x0d,
    /// Set accumulator to be the Nth Field of record at accumulator
    GetField          = 0x0e,
    /// Accumulator is an record; set its Nth field to be stack.pop()
    SetField          = 0x0f,
    /// Set accumulator to be a new record with tag N of size arg1 - REQUIRES arg1
    MakeBlock         = 0x10,
    /// Ensure the stack contains N arguments
    Grab              = 0x11,
    /// Must precede grab - returns to caller after grab posted more arguments
    Restart           = 0x12,
    /// pc += arg1 if accumulator is true/false/always
    Branch            = 0x14,
    /// Closure ( nvars, ofs )
    /// Creates a closure with an environment and nvars-1 arguments
    /// If nvars is 0 then it would seem to be broken
    /// The closure object created has the PC of PC+ofs, the environment from the accumulator,
    /// and any more captured arguments from the stack
    Closure       = 0x15,
    /// ClosureRec ( nvars, nfuncs, ofs+ )
    /// 
    /// Creates a recursive closure with an environment and nfuncs-1
    /// infix functions and nvars-1 arguments. If nvars is 0 then it
    /// would seem to be broken. The closure object created has the code value
    /// of PC+ofs, the environment from the accumulator, nfuncs-1
    /// infix records of (header, PC+ofs[nfunc]) which are pushed onto
    /// the stack (after argument popping) and any more captured
    /// arguments from the stack This instruction is presumably for
    /// sets of mutually recursive functions
    ClosureRec    = 0x16,
    /// Apply etc
    Apply         = 0x17, 
    ApplyN        = 0x18, 
    AppTerm       = 0x19, 
    Return        = 0x1a, 
    PushRetAddr   = 0x1b,
    AddToAcc      = 0x1c,
    AddToField0   = 0x1d,
    IsInt         = 0x1e,
}

//ip Opcode
impl Opcode {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Self {
        num::FromPrimitive::from_usize(n).unwrap()
    }
    pub fn uses_subop(&self) -> bool {
        match self {
            Self::LogicOp   => { true },
            Self::ArithOp   => { true },
            Self::IntCmp    => { true },
            Self::Branch    => { true },
            _ => { false },
        }
    }
    pub fn num_args(&self) -> usize {
        match self {
            Opcode::ArithOp             | // none
            Opcode::LogicOp             | // none
            Opcode::IntCmp              | // none
            Opcode::Restart             | // none
            Opcode::IsInt          => {   // none
                0
            }
            Opcode::Const               | // 1 - value to set
            Opcode::PushConst           | // 1 - value to set
            Opcode::Acc                 | // 1 - offset in stack
            Opcode::PushAcc             | // 1 - offset in stack
            Opcode::EnvAcc              | // 1 - offset in env
            Opcode::PushEnvAcc          | // 1 - offset in env
            Opcode::OffsetClosure       | // 1 - offset in closure (may be -ve)
            Opcode::PushOffsetClosure   | // 1 - offset in closure (may be -ve)
            Opcode::Pop                 | // 1 - number to pop   
            Opcode::Assign              | // 1 - offset in stack
            Opcode::AddToAcc            | // 1 - value to add
            Opcode::AddToField0         | // 1 - value to add
            Opcode::GetField            | // 1 - offset in record
            Opcode::SetField            | // 1 - offset in record
            Opcode::IntBranch           | // 1 - branch offset
            Opcode::Branch              | // 1 - branch offset
            Opcode::Grab                | // 1 - number of required arguments
            Opcode::Apply               | // 1 - number of extra args
            Opcode::ApplyN              | // 1 - number of extra args to replicate
            Opcode::Return              | // 1 - stack frame size
            Opcode::PushRetAddr     => { // 1 - branch offset
                1
            }
            Opcode::MakeBlock           | // 2 - tag and size
            Opcode::Closure             | // 2 - number of arguments, branch offset
            Opcode::AppTerm             | // 2 - number of args on stack, stack frame size
            Opcode::ClosureRec       => { // 2+ - number of arguments=N, N branch offsets
                2
            }
        }
    }
}


//a Traits - PicoStack, PicoValue, PicoHeap, PicoProgram, PicoCode, PicoTrace
//pt PicoStack

pub trait PicoStack<V> {
    //fp new
    //// Create a new stack
    fn new() -> Self;

    //mi get_relative
    /// Access the stack relative to the top
    ///
    /// An index of 0 is the top of the stack (i.e. stack.len()-1)
    /// An index of 1 is one value below, and so on
    fn get_relative(&self, index:usize) -> V;

    //mi set_relative
    /// Access the stack relative to the top
    ///
    /// An index of 0 is the top of the stack (i.e. stack.len()-1)
    /// An index of 1 is one value below, and so on
    fn set_relative(&mut self, index:usize, value:V);

    //mi shrink
    /// Shrink the stack by an amount
    fn shrink(&mut self, index:usize);

    //mi remove_slice
    /// Remove `amount` words that end `index` words from the top of the stack
    fn remove_slice(&mut self, index:usize, amount:usize);

    //mi pop
    /// Pop a value from the stack
    fn pop(&mut self) -> V;

    //mi push
    /// Push a value onto the stack
    fn push(&mut self, value:V);

    //zz All done{
}

//pt PicoValue
/// The value used by the interpreter.
///
/// The Ocaml machine used an integer of some size whose bottom bit is
/// 0 for an record (with the value being usable as an index); this
/// enables a garbage collector to scan the stack and heap objects for
/// references to heap objects, and therefore perform solid garbage collection
///
/// If an interpreter is very short-lived and does not require garbage
/// collection then the values could be untyped - there is one
/// instruction IsInt which is provided by the interpreter to
/// differentiate betweenn values and records, but that is not a
/// critical instruction.
///
/// Other mechanisms can be utilized also for garbage collection - all
/// object records point directly at a real object record header, so
/// any value that looks like it points to such a record could
/// pessimistically be deemed to be keeping that record alive.
pub trait PicoValue : Sized + Clone + Copy + std::fmt::Debug {
    type Stack : PicoStack<Self>;
    fn unit() -> Self;
    fn int(n:isize) -> Self;
    fn maybe_int(self) -> bool;
    fn maybe_record(self) -> bool { ! self.maybe_int() }
    fn is_false(self) -> bool;
    fn as_isize(self) -> isize;
    fn as_usize(self) -> usize;
    fn of_usize(usize) -> Self;
    fn as_pc(self) -> usize;
    fn of_pc(usize) -> Self;
    fn as_heap_index(self) -> usize; // Guaranteed to be invoked only if is_record

    fn bool_not(self) -> Self;
    fn negate(self) -> Self;
    fn add(self, other:Self) -> Self;
    fn sub(self, other:Self) -> Self;
    fn mul(self, other:Self) -> Self;
    fn div(self, other:Self) -> Self;
    fn rem(self, other:Self) -> Self;
    fn and(self, other:Self) -> Self;
    fn or(self, other:Self) -> Self;
    fn xor(self, other:Self) -> Self;
    fn lsl(self, other:Self) -> Self;
    fn lsr(self, other:Self) -> Self;
    fn asr(self, other:Self) -> Self;
    fn cmp_eq(self, other:Self) -> bool;
    fn cmp_ne(self, other:Self) -> bool;
    fn cmp_lt(self, other:Self) -> bool;
    fn cmp_le(self, other:Self) -> bool;
    fn cmp_gt(self, other:Self) -> bool;
    fn cmp_ge(self, other:Self) -> bool;
    fn cmp_ult(self, other:Self) -> bool;
    fn cmp_uge(self, other:Self) -> bool;
}

//pt PicoHeap
/// The trait that a Heap must support for the picointerpreter
///
/// Each heap object must consist of a header and a number of fields
/// The fields are accessed as a field offset from the header
/// Field 0 is the first field.
pub trait PicoHeap<V: PicoValue> : Sized {

    //fp new
    /// Create a new heap
    fn new() -> Self;

    //fp alloc_small
    /// Perform a small allocation in the heap; the size is known at
    /// compile time, and if a multi-size heap implementation is used
    /// then this can guarantee to be 'small' - e.g. for a closure.
    fn alloc_small(&mut self, tag:usize, n:usize) -> V;

    //fp alloc_small
    /// Perform a small allocation in the heap; the size is known at
    fn alloc(&mut self, tag:usize, n:usize)       -> V;

    //fp get_tag
    /// Retrieve the tag - notionally a Tag, but usize to accommodate custom tags
    fn get_tag(&self, record:V)      -> usize;

    //fp get_record_size
    /// Retrieve the size in words of a record
    /// this should be the size requested at allocation
    fn get_record_size(&self, record:V)      -> usize;

    //fp get_field
    /// Retrieve the value from a field of an record. This may be an
    /// integer, for example, or an record, but it will not be a
    /// PC.
    fn get_field(&self, record:V, ofs:usize)      -> V;

    //fp set_field
    /// Set the field of an record to a value; this value may be an
    /// integer, for example, or an record; it will not be a PC
    fn set_field(&mut self, record:V, ofs:usize, data:V);

    //fp set_code_val
    /// Store a PC in the field of an record; used particularly to
    /// store the PC in an environment or closure
    fn set_code_val(&mut self, record:V, ofs:usize, data:usize);

    //fp get_code_val
    /// Retrieve a PC from an record and offset; used particularly to
    /// retreive the PC from an environment or closure
    fn get_code_val(&self, record:V, ofs:usize) -> usize;

    //fp set_infix_record
    /// Set the fields of a Closure record to make an 'infix' record
    /// at an offset, and of a specified size, with a specified PC
    ///
    /// The infix records is a header and a single field. This field
    /// will be a code value. The header encodes how deep inside the
    /// closure the infixe header is - it is a 'upward' reference, in
    /// essence. The first infix in a closure has size 2; the second
    /// size 4, and so on.
    ///
    fn set_infix_record(&mut self, record:V, ofs:usize, size:usize, data:usize) -> V;

    //zz All done
}

//pt PicoProgram
/// The trait of a program of PicoCode.
///
/// It will usually be some form of array of PicoCode values, but the
/// packing mechanism for the code is up to the trait object
pub trait PicoProgram : Sized {
    type Code: PicoCode;
    fn new() -> Self;
    //fp fetch_instruction
    fn fetch_instruction(&self, pc:usize) -> Self::Code;
    /// Used when the code element is an offset to e.g. the stack
    /// Invoked in order of arguments after fetch_instruction, and all arguments SHALL be requested
    fn arg_as_usize(&self, code:&mut Self::Code, pc:usize, arg:usize, ) -> usize;
    /// Used when the code element is a branch offset
    /// Invoked in order of arguments after fetch_instruction, and all arguments SHALL be requested
    fn arg_as_isize(&self, code:&mut Self::Code, pc:usize, arg:usize) -> isize;
    /// Move to the next pc
    fn next_pc(&self, code:&Self::Code, pc:usize, num_args:usize) -> usize;
    /// Used when the code element is a branch offset
    fn branch_pc(&self, code:&Self::Code, pc:usize, ofs:usize) -> usize;
}

//pt PicoCode
/// A picocode encoded value, with mechanisms to break it in to opcode,
/// immediate value, and to get integer values from it as isize or
/// usize
///
/// The PicoCode is tied to a program, so that the length of a
/// PicoCode intepreted instruction can be a variable number of
/// PicoCode elements; this permits tightly packet bytecode.
pub trait PicoCode : Clone + Copy + Sized + std::fmt::Debug + std::fmt::Display {
    /// Opcode class for the instruction encoding
    fn opcode(self) -> Opcode;
    /// Used to retrieve the subopcode immediate value - only permitted if it has one
    fn subop(self) -> usize;
    /// Size of restart instruction so Grab can go back ahead of it
    fn sizeof_restart() -> usize;
}

//pt PicoTrace
pub trait PicoTrace {
    type Program : PicoProgram;
    fn new() -> Self;
    fn trace_fetch(&mut self, program:&Self::Program, pc:usize);
}

//a PicoTag - Record tags
/// The base tags for an record, required by the intepreter
/// Actual implementations may use a superset
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum PicoTag {
    /// A closure record consisting of the fields:
    /// [0]      => PC of code for the closure
    /// [1]      => environment record for the closure
    /// [2..N+1] => first N arguments for the closure
    /// A closure record is invoked with M>=1 more arguments on the stack 
    Closure,
    /// Infix records are somewhat magic
    /// They are only permitted to occur in a Closure
    /// The tag is associated with a length in words
    Infix,
    // ? Vec     = 0x1,
}
//ip PicoTag
impl PicoTag {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Option<Self> {
        num::FromPrimitive::from_usize(n)
    }
}

