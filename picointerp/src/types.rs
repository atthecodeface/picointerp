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
//tp IntOp
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum IntOp {
 Neg  = 0,
 Add  = 1,
 Sub  = 2,
 Mul  = 3,
 Div  = 4,
 Mod  = 5,
 And  = 6,
 Or   = 7,
 Xor  = 8,
 Lsl  = 9,
 Lsr  = 10,
 Asr  = 11,
}
//ip IntOp
impl IntOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Option<Self> {
        num::FromPrimitive::from_usize(n)
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
    pub fn of_usize(n:usize) -> Option<Self> {
        num::FromPrimitive::from_usize(n)
    }
}

//tp Opcode
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum Opcode {
    /// Set accumulator to a constant integer value from code or immediate
    Const      = 0x00, // Ocaml: imm of 0-3 or integer value
    /// Push accumulator the set accumulator to a constant
    PushConst  = 0x01, // Ocaml: imm of 0-3 or integer value
    /// Set accumulator to the stack at an offset
    Acc        = 0x02, // Ocaml: imm of 0-7 or integer value
    /// Push accumulator the set accumulator to the stack at an offset
    PushAcc    = 0x03, // Ocaml: N = offset in to stack
    /// Set accumulator to the Nth environment field
    EnvAcc     = 0x04, // Ocaml: imm of 0-4 or integer value
    /// Push accumulator the set accumulator to the Nth environment field
    PushEnvAcc = 0x05, // Ocaml: N = offset in to stack
    /// Pop N, from an immediate or next code
    Pop        = 0x06, // N = usize to adjust stack by
    /// Assign stack[offset] to the accumulatore
    Assign     = 0x07, // N = offset in to stack
    /// accumulator OP stack.pop() -- which OP is immediate - no pop for NEG
    IntOp      = 0x08, // immediate value is type of int operation
    /// accumulator CMP stack.pop() -- which OP is immediate
    IntCmp     = 0x09, // N => eq, ne, lt, le, gt, ge, ult, uge,
    /// accumulator CMP stack.pop() -- which OP is immediate - and branch by arg1
    IntBranch  = 0x0a, // N => eq, ne, lt, le, gt, ge, ult, uge - REQUIRES arg1
    /// Set accumulator to be the Nth Field of object at accumulator
    GetField   = 0x0b, // accumulator = Field_of(accumulator, N) - accumulator should be a heap object
    /// Accumulator is an object; set its Nth field to be stack.pop()
    SetField   = 0x0c,
    /// Set accumulator to be a new object with tag N of size arg1 - REQUIRES arg1
    MakeBlock  = 0x0d, // accumulator = Alloc(tag=N, size=arg1)
    /// Ensure 
    Grab       = 0x0e, // accumulator = Alloc(tag=N, size=arg1)
    /// accumulator = not accumulator
    BoolNot       = 0x0f,
    /// pc += arg1 - REQUIRES arg1
    Branch        = 0x10,
    /// if accumulator is false, pc += arg1 - REQUIRES arg1
    BranchIfNot   = 0x11,
    /// if accumulator is true, pc += arg1 - REQUIRES arg1
    BranchIf      = 0x12,
    /*
* OffsetInt(N) : accumulator += N
* IsInt(N) : accumulator = { if accumulator is integer {1} else {0} }
* OffsetRef(N) : Field(accumulator, 0) += N; accumulator = Unit
* Apply(N) : extra_args=N-1, PC=accumulator.as_env(0), env=accumulator
* ApplyN : N=1-4; extra_args=N-1, PC=accumulator.as_env(0), env=accumulator, stack.push( extra_args, env, PC, stack[0..N-1])
* AppTermN(X): N=1-4; Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)
* AppTerm(N, X): Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)
* PushRetAddr(N) : stack.push( extra_args, env, PC+N )
* Grab
* Restart
* Return(X): stack.adjust(-X); if extra_args>0 {Apply(extra_args)} else { pc,env,extra_args=stack.pop(3); }
* Closure(0,N): accumulator = Alloc(closure,1), accumulator.as_env(0)=PC+N
* Closure(M,N): stack.push(accumulator), accumulator = Alloc(closure,1+M), accumulator.as_env([0..M+1]) = (PC, stack.pop(M))
*/
}

//ip Opcode
impl Opcode {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Option<Self> {
        num::FromPrimitive::from_usize(n)
    }
    pub fn num_args(&self, is_imm:bool, imm:usize) -> usize {
        match self {
            Self::Const     => { if is_imm {0} else {1} },
            Self::Acc       => { if is_imm {0} else {1} },
            Self::PushConst => { if is_imm {0} else {1} },
            Self::PushAcc   => { if is_imm {0} else {1} },
            Self::Pop       => { 1 },
            Self::Assign    => { 1 },
            Self::IntOp     => { 0 },
            Self::IntCmp     => { 0 },
            Self::IntBranch  => { 1 },
            _ => { 0 },
        }
    }
}


//a Traits - PicoValue, PicoHeap, PicoCode
//pt PicoValue
/// The value used by the interpreter this is notionally forced to be an integer of some size whose bottom bit is 0 for an object (with the value being usable as an index)
pub trait PicoValue : Sized + Clone + Copy + std::fmt::Debug {
    fn unit() -> Self;
    fn int(n:isize) -> Self;
    fn is_int(self) -> bool;
    fn is_false(self) -> bool;
    fn is_object(self) -> bool { ! self.is_int() }
    fn as_isize(self) -> isize;
    fn as_usize(self) -> usize;
    fn as_heap_index(self) -> usize; // Guaranteed to be invoked only if is_object

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

//pt PicoCode
/// A picocode encoded value, with mechanisms to break it in to opcode,
/// immediate value, and to get integer values from it as isize or
/// usize
pub trait PicoCode : Clone + Copy + Sized + std::fmt::Debug + std::fmt::Display + PicoValue {
    /// Opcode class for the instruction encoding, and amount to increase PC by
    fn opcode_class_and_length(self) -> (Opcode, usize);
    /// Opcode class for the instruction encoding
    fn opcode_class(self) -> Opcode;
    /// Returns true if the instruction is an immediate operation
    fn code_is_imm(self) -> bool;
    /// Used to retrieve an immediate value - which may be shorter than as_value
    fn code_imm_value(self) -> Self;
    /// Used to retrieve an immediate value as a usize (e.g. stack offset)
    fn code_imm_usize(self) -> usize;
    /// Used when the code element contains e.g. a *pvalue* int
    fn code_as_value(self) -> Self;
    /// Used when the code element is an offset to e.g. the stack
    fn code_as_usize(self) -> usize;
    /// Used to convert a labeled instruction for a value to a vector of encodings (PicoCode)
    fn of_instruction(inst:&LabeledInstruction<Self>) -> Result<Vec<Self>,String>;
}

//pt PicoHeap
/// An implementation of a heap
pub trait PicoHeap<V: PicoValue> : Sized {
    fn new() -> Self;
    fn alloc_small(&mut self, tag:usize, n:usize) -> V;
    fn alloc(&mut self, tag:usize, n:usize)       -> V;
    fn get_field(&self, object:V, ofs:usize)      -> V;
    fn set_field(&mut self, object:V, ofs:usize, data:V);
}

//pt Label
#[derive(Debug)]
pub enum Label {
    None,
    Id(String),
    Offset(isize),
    Address(usize),
}

//ip Label
impl Label {
    //mp as_str
    /// Return a string of the label for assembly/disassembly - perhaps relative to PC in the future
    pub fn as_str(&self) -> String {
        match &self {
            Label::None => {
                String::new()
            },
            Label::Id(s) => {
                format!("{}: ",s)
            },
            Label::Offset(s) => {
                format!("+{}: ",s)
            },
            Label::Address(s) => {
                format!("{} ",s)
            },
        }
    }
    
    //zz All done
}

//pt LabeledInstruction
#[derive(Debug)]
pub struct LabeledInstruction<V:PicoCode> {
    pub label     : Label,
    pub opcode    : Option<Opcode>,
    pub immediate : Option<usize>, // contains IntOp for an Opcode::IntOp
    pub arg1      : Option<V>,
    pub arg2      : Option<V>,
    pub target    : Label,
    pub comment   : Option<String>,
}

//ip LabeledInstruction<V>
impl <V:PicoCode> LabeledInstruction<V> {
    //fp new
    pub fn new() -> Self {
        Self {
            label  : Label::None,
            opcode : None,
            immediate : None,
            arg1 : None,
            arg2 : None,
            target : Label::None,
            comment : None,
        }
    }
    //fp make
    pub fn make(opcode:Opcode, immediate:Option<usize>, arg1:Option<V> ) -> Self {
        Self {
            label  : Label::None,
            opcode : Some(opcode),
            immediate, arg1,
            arg2 : None,
            target : Label::None,
            comment : None,
        }
    }
    //zz All done
}

//pt Encoding
pub trait Encoding<V:PicoCode> {
    //fp to_instruction
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_instruction(code:&Vec<V>, ofs:usize) -> Result<(LabeledInstruction<V>, usize),String> {
        match code.get(ofs) {
            None => Err(format!("Offset {} outside bounds of code",ofs)),
            Some(v) => {
                let mut instruction = LabeledInstruction::new();
                let opcode  = v.opcode_class();
                let is_imm  = v.code_is_imm();
                let imm     = v.code_imm_usize();
                instruction.opcode = Some(opcode);
                if is_imm {
                    instruction.immediate = Some(imm);
                }
                let num_args = opcode.num_args(is_imm, imm);
                if num_args > 0 {
                    if let Some(data) = code.get(ofs+1) {
                        instruction.arg1 = Some(*data);
                    } else {
                        return Err(format!("Offset {} for first data value is outside bounds of code",ofs+1));
                    }
                }
                if num_args > 1 {
                    if let Some(data) = code.get(ofs+2) {
                        instruction.arg2 = Some(*data);
                    } else {
                        return Err(format!("Offset {} for second data value is outside bounds of code",ofs+2));
                    }
                }
                Ok((instruction, num_args+1))
            }
        }
    }

}

