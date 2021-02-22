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

@file    picointerp.rs
@brief   Picointerpreter
 */

//a Imports
use super::types::*;

//a PicoInterp
//tp PicoInterp
/// A picointerpreter with a reference to the code it has, which then
/// contains its heap and values
pub struct PicoInterp<'a, V:PicoCode, H:PicoHeap<V>> {
    code : &'a Vec<V>,
    heap : H,
    stack : Vec<V>,
    pc : usize,
    extra_args : usize,
    env  : V,
    accumulator : V,
}

//ip PicoInterp
impl <'a, V:PicoCode, H:PicoHeap<V>, > PicoInterp<'a, V, H> {

    //fp new
    /// Create a new picointerpreter for a piece of code
    pub fn new(code : &'a Vec<V>) -> Self {
        let heap = H::new();
        let stack = Vec::new();
        let env = V::unit();
        let accumulator = V::int(0);
        Self { code, heap, stack, pc:0, extra_args:0, env, accumulator }
    }

    //mp get_pc
    pub fn get_pc(&self) -> usize { self.pc }

    //mp get_accumulator
    pub fn get_accumulator(&self) -> V { self.accumulator }

    //mp run_code
    pub fn run_code(&mut self, n:usize) {
        for _ in 0..n {
            self.execute();
        }
    }

    //mi execute
    #[inline]
    fn execute(&mut self) {
        let pc = self.pc;
        let instruction  = self.code[pc]; // PicoCode
        match instruction.opcode_class() {
            Opcode::Const => {
                self.accumulator = self.data_value(instruction);
            }
            Opcode::PushConst => {
                self.stack.push(self.accumulator);
                self.accumulator = self.data_value(instruction);
            }
            Opcode::Acc => {
                let ofs = self.data_usize(instruction);
                let sp = self.stack.len();
                self.accumulator = self.stack[sp -1 - ofs];
            }
            Opcode::PushAcc => {
                self.stack.push(self.accumulator);
                let ofs = self.data_usize(instruction);
                let sp = self.stack.len();
                self.accumulator = self.stack[sp -1 - ofs];
            }
            Opcode::Pop => {
                let ofs = self.data_usize(instruction);
                let sp = self.stack.len() - ofs;
                self.stack.truncate(sp);
            }
            Opcode::Assign => {
                let ofs = self.data_usize(instruction);
                let sp = self.stack.len();
                self.stack[sp-1-ofs] = self.accumulator;
                self.accumulator = V::unit();
            }
            Opcode::IntOp => {
                self.pc += 1;
                let int_op = instruction.code_imm_usize();
                self.do_int_op(int_op & 0xf);
            }
            Opcode::IntCmp => {
                self.pc += 1;
                let cmp_op = instruction.code_imm_usize();
                self.accumulator = V::int( if self.do_cmp_op(cmp_op & 0xf) {1} else {0} );
            }
            Opcode::IntBranch => {
                self.pc += 2;
                let cmp_op = instruction.code_imm_usize();
                if self.do_cmp_op(cmp_op & 0xf) {
                    self.pc = self.code[self.pc-1].code_as_usize();
                }
            }
            Opcode::GetField => {
                let ofs = self.data_usize(instruction);
                self.accumulator = self.heap.get_field(self.accumulator, ofs);
            }
            _ => {
                self.pc += 1;
            }
        }
    }

    //mi data_usize - adjusts PC
    #[inline]
    fn data_usize(&mut self, instruction:V) -> usize {
        if instruction.code_is_imm() {
            self.pc += 1;
            instruction.code_imm_usize()
        } else {
            self.pc += 2;
            self.code[self.pc-1].code_as_usize()
        }
    }
    
    //mi data_value - adjusts PC
    #[inline]
    fn data_value(&mut self, instruction:V) -> V {
        if instruction.code_is_imm() {
            self.pc += 1;
            instruction.code_imm_value()
        } else {
            self.pc += 2;
            self.code[self.pc-1].code_as_value()
        }
    }
    
    //mi do_int_op
    #[inline]
    fn do_int_op(&mut self, int_op:usize) {
        match IntOp::of_usize(int_op).unwrap() {
            IntOp::Neg => { self.accumulator = self.accumulator.negate(); },
            IntOp::Add => { self.accumulator = self.accumulator.add(self.stack.pop().unwrap()); },
            IntOp::Sub => { self.accumulator = self.accumulator.sub(self.stack.pop().unwrap()); },
            IntOp::Mul => { self.accumulator = self.accumulator.mul(self.stack.pop().unwrap()); },
            IntOp::Div => { self.accumulator = self.accumulator.div(self.stack.pop().unwrap()); },
            IntOp::Mod => { self.accumulator = self.accumulator.rem(self.stack.pop().unwrap()); },
            IntOp::And => { self.accumulator = self.accumulator.and(self.stack.pop().unwrap()); },
            IntOp::Or  => { self.accumulator = self.accumulator.or (self.stack.pop().unwrap()); },
            IntOp::Xor => { self.accumulator = self.accumulator.xor(self.stack.pop().unwrap()); },
            IntOp::Lsl => { self.accumulator = self.accumulator.asr(self.stack.pop().unwrap()); },
            IntOp::Lsr => { self.accumulator = self.accumulator.lsr(self.stack.pop().unwrap()); },
            IntOp::Asr => { self.accumulator = self.accumulator.asr(self.stack.pop().unwrap()); },
            // _ => { self.accumulator = self.accumulator.negate(); },
        }
    }
    
    //mi do_cmp_op
    #[inline]
    fn do_cmp_op(&mut self, cmp_op:usize) -> bool {
        match CmpOp::of_usize(cmp_op).unwrap() {
            CmpOp::Eq  => { self.accumulator.cmp_eq(self.stack.pop().unwrap()) },
            CmpOp::Ne  => { self.accumulator.cmp_ne(self.stack.pop().unwrap()) },
            CmpOp::Lt  => { self.accumulator.cmp_lt(self.stack.pop().unwrap()) },
            CmpOp::Le  => { self.accumulator.cmp_le(self.stack.pop().unwrap()) },
            CmpOp::Gt  => { self.accumulator.cmp_gt(self.stack.pop().unwrap()) },
            CmpOp::Ge  => { self.accumulator.cmp_ge(self.stack.pop().unwrap()) },
            CmpOp::Ult => { self.accumulator.cmp_ult(self.stack.pop().unwrap()) },
            CmpOp::Uge => { self.accumulator.cmp_uge(self.stack.pop().unwrap()) },
        }
    }
    
    //zz All done
}

