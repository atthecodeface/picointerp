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
//a Instruction enumeration
//pt IntOp
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

impl IntOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Option<Self> {
        num::FromPrimitive::from_usize(n)
    }
}

//pt CmpOp
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

impl CmpOp {
    pub fn as_usize(&self) -> usize {
        num::ToPrimitive::to_usize(self).unwrap()
    }
    pub fn of_usize(n:usize) -> Option<Self> {
        num::FromPrimitive::from_usize(n)
    }
}

//pt Opcode
#[derive(Clone, Copy, PartialEq, Debug, FromPrimitive, ToPrimitive)]
pub enum Opcode {
    /// Set accumulator to a constant integer value from code or immediate
    Const     = 0x00, // Ocaml: imm of 0-3 or integer value
    /// Set accumulator to the stack at an offset
    Acc       = 0x01, // Ocaml: imm of 0-7 or integer value
    /// Push accumulator the set accumulator to a constant
    PushConst = 0x02, // Ocaml: imm of 0-3 or integer value
    /// Push accumulator the set accumulator to the stack at an offset
    PushAcc   = 0x03, // Ocaml: N = offset in to stack
    /// Pop N, from an immediate or next code
    Pop       = 0x04, // N = usize to adjust stack by
    /// Assign stack[offset] to the accumulatore
    Assign    = 0x05, // N = offset in to stack
    /// accumulator OP stack.pop() -- which OP is immediate - no pop for NEG
    IntOp     = 0x06, // immediate value is type of int operation
    /// accumulator CMP stack.pop() -- which OP is immediate
    IntCmp    = 0x07, // N => eq, ne, lt, le, gt, ge, ult, uge,
    IntBranch = 0x08, // N => eq, ne, lt, le, gt, ge, ult, uge,
    /*
* OffsetInt(N) : accumulator += N
* IsInt(N) : accumulator = { if accumulator is integer {1} else {0} }
* OffsetRef(N) : Field(accumulator, 0) += N; accumulator = Unit
* EnvAccN: N=1-4; Accumulator = Field(env, N)
* EnvAcc(N): Accumulator = Field(env, N)
* PushEnvAccN: N=1-4; Push accumulator, accumulator = Field(env, N)
* PushEnvAcc(N): Push accumulator, accumulator = Field(env, N)
* Apply(N) : extra_args=N-1, PC=accumulator.as_env(0), env=accumulator
* ApplyN : N=1-4; extra_args=N-1, PC=accumulator.as_env(0), env=accumulator, stack.push( extra_args, env, PC, stack[0..N-1])
* AppTermN(X): N=1-4; Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)
* AppTerm(N, X): Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)
* PushRetAddr(N) : stack.push( extra_args, env, PC+N )
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

