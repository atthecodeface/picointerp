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
pub struct PicoInterp<'a, C:PicoCode, V:PicoValue, H:PicoHeap<V>> {
    code : &'a C::Program,
    heap : H,
    stack : V::Stack,
    pc : usize,
    extra_args : usize,
    env         : V,
    accumulator : V,
}

//ip PicoInterp
impl <'a, C:PicoCode, V:PicoValue, H:PicoHeap<V>, > PicoInterp<'a, C, V, H> {

    //fp new
    /// Create a new picointerpreter for a piece of code
    pub fn new(code : &'a C::Program) -> Self {
        let heap = H::new();
        let stack = V::Stack::new();
        let env = V::unit();
        let accumulator = V::int(0);
        Self { code, heap, stack, pc:0, extra_args:0, env, accumulator }
    }

    //mp set_pc
    pub fn set_pc(&mut self, pc:usize) {
        self.pc = pc;
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
        let mut instruction  = self.code.fetch_instruction(self.pc);
        match instruction.opcode_class() {
            //cc Const/Acc/Envacc + Push variants
            Opcode::Const => {
                self.accumulator = V::int(instruction.arg_as_isize(self.code, self.pc, 0));
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::PushConst => {
                self.stack.push(self.accumulator);
                self.accumulator = V::int(instruction.arg_as_isize(self.code, self.pc, 0));
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::Acc => {
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.accumulator = self.stack.get_relative(ofs);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::PushAcc => {
                self.stack.push(self.accumulator);
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.accumulator = self.stack.get_relative(ofs);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::EnvAcc => {
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.accumulator = self.heap.get_field(self.env, ofs);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::PushEnvAcc => {
                self.stack.push(self.accumulator);
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.accumulator = self.heap.get_field(self.env, ofs);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            //cc Pop, Assign
            Opcode::Pop => {
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.stack.shrink(ofs);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::Assign => {
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.stack.set_relative(ofs, self.accumulator);
                self.accumulator = V::unit();
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            //cc LogicOp/ArithOp/IntCmp/IntBranch
            Opcode::ArithOp => {
                let int_op = instruction.subop();
                self.do_arith_op(int_op);
                self.pc = instruction.next_pc(self.code, self.pc, 0);
            }
            Opcode::LogicOp => {
                let int_op = instruction.subop();
                self.do_logic_op(int_op);
                self.pc = instruction.next_pc(self.code, self.pc, 0);
            }
            Opcode::IntCmp => {
                let cmp_op = instruction.subop();
                self.accumulator = V::int( if self.do_cmp_op(cmp_op & 0xf) {1} else {0} );
                self.pc = instruction.next_pc(self.code, self.pc, 0);
            }
            Opcode::IntBranch => {
                let cmp_op = instruction.subop();
                // Arg must ALWAYS be fetched
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                if self.do_cmp_op(cmp_op) {
                    self.pc = instruction.branch_pc(self.code, self.pc, ofs);
                } else {
                    self.pc = instruction.next_pc(self.code, self.pc, 1);
                }
            }
            //cc Create record and field access
            Opcode::GetField => {
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                self.accumulator = self.heap.get_field(self.accumulator, ofs);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::SetField => {
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                let data = self.stack.pop();
                self.heap.set_field(self.accumulator, ofs, data);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::MakeBlock => {
                let tag  = instruction.arg_as_usize(self.code, self.pc, 0);
                let size = instruction.arg_as_usize(self.code, self.pc, 1);
                let record = self.heap.alloc(tag, size);
                self.heap.set_field(record, 0, self.accumulator);
                for i in 1..size {
                    let data = self.stack.pop();
                    self.heap.set_field(record, i, data);
                }
                self.accumulator = record;
                self.pc = instruction.next_pc(self.code, self.pc, 2);
            }
            //cc BoolNot and Branch
            Opcode::Branch => {
                let taken = {
                    match BranchOp::of_usize(instruction.subop()) {
                        BranchOp::Eq => { !self.accumulator.is_false() },
                        BranchOp::Ne => { self.accumulator.is_false()  },
                        _ => true
                    }
                };
                // Argument must ALWAYS be fetched
                let ofs = instruction.arg_as_usize(self.code, self.pc, 0);
                if taken {
                    self.pc = instruction.branch_pc(self.code, self.pc, ofs);
                } else {
                    self.pc = instruction.next_pc(self.code, self.pc, 1);
                }
            }
            //cc Grab and Restart
            Opcode::Grab => {
                let required_args = instruction.arg_as_usize(self.code, self.pc, 0);
                // extra_args is number of args on the stack on top of the standard 1
                println!("reqd: {} extra:{}", required_args, self.extra_args);
                if self.extra_args >= required_args {
                    // Got enough - so we are going to just keep going and use them!
                    self.extra_args -= required_args;
                    self.pc = instruction.next_pc(self.code, self.pc, 1);
                } else {
                    let num_args = 1 + self.extra_args;
                    self.accumulator = self.heap.alloc_small(Tag::Closure.as_usize(), 2+num_args);
                    self.heap.set_field(self.accumulator, 1, self.env);
                    for i in 0..num_args {
                        let data = self.stack.pop();
                        self.heap.set_field(self.accumulator, i+2, data);
                    }
                    self.heap.set_code_val(self.accumulator, 0, self.pc - C::sizeof_restart());
                    self.extra_args  = self.stack.pop().as_usize();
                    self.env         = self.stack.pop();
                    self.pc          = self.stack.pop().as_pc();
                }
            }
            Opcode::Restart => {
                let num_args = self.heap.get_record_size(self.env) - 2;
                for i in 0..num_args {
                    self.stack.push( self.heap.get_field(self.env, i+2) );
                }
                self.env = self.heap.get_field(self.env, 1);
                self.extra_args += num_args;
                self.pc = instruction.next_pc(self.code, self.pc, 0);
            }
            //cc Closures
            Opcode::Closure => {
                let nvars = instruction.arg_as_usize(self.code, self.pc, 0);
                let ofs   = instruction.arg_as_usize(self.code, self.pc, 1);
                println!("Closure of {:x} {:x}",nvars, ofs);
                if nvars > 0 { self.stack.push(self.accumulator); }
                self.accumulator = self.heap.alloc_small(Tag::Closure.as_usize(), 1+nvars);
                self.heap.set_code_val(self.accumulator, 0, self.pc.wrapping_add(ofs));
                for i in 0..nvars {
                    let data = self.stack.pop();
                    self.heap.set_field(self.accumulator, i + 1, data );
                }
                self.pc = instruction.next_pc(self.code, self.pc, 2);
            }
            Opcode::ClosureRec => {
                let nfuncs = instruction.arg_as_usize(self.code, self.pc, 0); // will be >=1
                let nvars  = instruction.arg_as_usize(self.code, self.pc, 1); // will be >=1
                let ofs    = instruction.arg_as_usize(self.code, self.pc, 2);
                if nvars > 0 { self.stack.push(self.accumulator); }
                self.accumulator = self.heap.alloc_small(Tag::Closure.as_usize(), nvars + nfuncs*2 - 1 );
                self.heap.set_code_val(self.accumulator,  0, self.pc.wrapping_add(ofs));
                let arg_offset = 1 + ((nfuncs-1) * 2);
                for i in 0..nvars {
                    let data = self.stack.pop();
                    self.heap.set_field(self.accumulator, i + arg_offset, data );
                }
                let rec_offset = 1;
                for i in 0..nfuncs-1 {
                    let ofs    = instruction.arg_as_usize(self.code, self.pc, 3+i);
                    let infix_obj = self.heap.set_infix_record(self.accumulator, i*2 + rec_offset, (i*2)+2, self.pc.wrapping_add(ofs));
                    self.stack.push(infix_obj);
                }
                self.pc = instruction.next_pc(self.code, self.pc, nfuncs+2);
            }
            //cc AddToAcc AddToField0 IsInt
            Opcode::AddToAcc => {
                let value = V::int(instruction.arg_as_isize(self.code, self.pc, 0));
                self.accumulator = self.accumulator.add(value);
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::IsInt => {
                if self.accumulator.is_int() {
                    self.accumulator = V::int(1);
                } else {
                    self.accumulator = V::int(0);
                }
                self.pc = instruction.next_pc(self.code, self.pc, 0);
            }
            Opcode::AddToField0 => {
                let value = V::int(instruction.arg_as_isize(self.code, self.pc, 0));
                let mut data = self.heap.get_field(self.accumulator, 0);
                data = data.add(value);
                self.heap.set_field(self.accumulator, 0, data);
                self.accumulator = V::unit();
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            //cc OffsetClosure + Push variants
            Opcode::OffsetClosure => { // 0, 2, 4, N
                let value = V::int(instruction.arg_as_isize(self.code, self.pc, 0));
                assert_eq!(value.as_usize(), 0);
                self.accumulator = self.env; // + ofs.as_usize();
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            Opcode::PushOffsetClosure => {
                self.stack.push(self.accumulator);
                let value = V::int(instruction.arg_as_isize(self.code, self.pc, 0));
                assert_eq!(value.as_usize(), 0);
                self.accumulator = self.env; // + ofs.as_usize();
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
            //cc Function invocation - Apply, AppTerm
            // Apply
            Opcode::Apply => {
                self.extra_args = instruction.arg_as_usize(self.code, self.pc, 0) - 1;
                self.pc = self.heap.get_code_val(self.accumulator, 0);
                self.env = self.accumulator;
                println!("Applied {:?} {:?} {:?}",self.env,self.heap.get_code_val(self.accumulator,0), self.heap.get_code_val(self.accumulator,1), );
            }
            Opcode::ApplyN => {
                // accumulator = environment to call (with PC at field 0)
                // stack = N arguments (N>=1)
                // replicate N of stack
                // push PC+env+extra_args
                // get pc+env from closure and extra_args = N-1
                // Do Push(arguments)
                let num_args   = instruction.arg_as_usize(self.code, self.pc, 0);
                for _ in 0..num_args {
                    self.stack.push(self.stack.get_relative(num_args-1));
                }
                // Do PushRetAddr of *this* PC
                self.stack.push(V::of_pc(self.pc));
                self.stack.push(self.env);
                self.stack.push(V::of_usize(self.extra_args));
                // Jump to Closure
                self.pc         = self.heap.get_field(self.accumulator, 0).as_pc();
                self.env        = self.accumulator;
                self.extra_args = num_args-1;
            }
            Opcode::AppTerm => {
                // accumulator = environment to call (with PC at field 0)
                // stack = N arguments
                // Must pop this stack frame (size provided) which
                // is above the N arguments on the stack!
                let num_args   = instruction.arg_as_usize(self.code, self.pc, 0);
                let frame_size = instruction.arg_as_usize(self.code, self.pc, 1);
                self.stack.remove_slice(num_args, frame_size);
                // Jump to Closure
                self.pc  = self.heap.get_field(self.accumulator, 0).as_pc();
                self.env = self.accumulator;
                self.extra_args += num_args-1;
            }
            Opcode::Return => {
                let frame_size = instruction.arg_as_usize(self.code, self.pc, 0);
                self.stack.shrink(frame_size);
                if self.extra_args > 0 { // return but the next argument is there already
                    self.extra_args -= 1;
                    self.pc  = self.heap.get_field(self.accumulator, 0).as_pc();
                    self.env = self.accumulator;
                } else { // return properly
                    self.extra_args  = self.stack.pop().as_usize();
                    self.env         = self.stack.pop();
                    self.pc          = self.stack.pop().as_pc();
                }
            }
            Opcode::PushRetAddr => {
                println!("PushRetAddr");
                let ofs    = instruction.arg_as_usize(self.code, self.pc, 0);
                // Do PushRetAddr (PC+ofs)
                self.stack.push(V::of_pc(self.pc.wrapping_add(ofs)));
                self.stack.push(self.env);
                self.stack.push(V::of_usize(self.extra_args));
                self.pc = instruction.next_pc(self.code, self.pc, 1);
            }
/*
    Instruct(SWITCH): {
      uint32 sizes = *pc++;
      if (Is_block(accu)) {
        intnat index = Tag_val(accu);
        Assert ((uintnat) index < (sizes >> 16));
        pc += pc[(sizes & 0xFFFF) + index];
      } else {
        intnat index = Long_val(accu);
        Assert ((uintnat) index < (sizes & 0xFFFF)) ;
        pc += pc[index];
      }
      Next;
    }*/
        }
    }

    //mi do_logic_op
    #[inline]
    fn do_logic_op(&mut self, logic_op:usize) {
        match LogicOp::of_usize(logic_op) {
            LogicOp::BoolNot => { self.accumulator = self.accumulator.bool_not(); },
            LogicOp::And     => { self.accumulator = self.accumulator.and(self.stack.pop()); },
            LogicOp::Or      => { self.accumulator = self.accumulator.or (self.stack.pop()); },
            LogicOp::Xor     => { self.accumulator = self.accumulator.xor(self.stack.pop()); },
            LogicOp::Lsl     => { self.accumulator = self.accumulator.asr(self.stack.pop()); },
            LogicOp::Lsr     => { self.accumulator = self.accumulator.lsr(self.stack.pop()); },
            LogicOp::Asr     => { self.accumulator = self.accumulator.asr(self.stack.pop()); },
        }
    }
    
    //mi do_arith_op
    #[inline]
    fn do_arith_op(&mut self, arith_op:usize) {
        match ArithOp::of_usize(arith_op) {
            ArithOp::Neg => { self.accumulator = self.accumulator.negate(); },
            ArithOp::Add => { self.accumulator = self.accumulator.add(self.stack.pop()); },
            ArithOp::Sub => { self.accumulator = self.accumulator.sub(self.stack.pop()); },
            ArithOp::Mul => { self.accumulator = self.accumulator.mul(self.stack.pop()); },
            ArithOp::Div => { self.accumulator = self.accumulator.div(self.stack.pop()); },
            ArithOp::Mod => { self.accumulator = self.accumulator.rem(self.stack.pop()); },
        }
    }
    
    //mi do_cmp_op
    #[inline]
    fn do_cmp_op(&mut self, cmp_op:usize) -> bool {
        match CmpOp::of_usize(cmp_op) {
            CmpOp::Eq  => { self.accumulator.cmp_eq(self.stack.pop()) },
            CmpOp::Ne  => { self.accumulator.cmp_ne(self.stack.pop()) },
            CmpOp::Lt  => { self.accumulator.cmp_lt(self.stack.pop()) },
            CmpOp::Le  => { self.accumulator.cmp_le(self.stack.pop()) },
            CmpOp::Gt  => { self.accumulator.cmp_gt(self.stack.pop()) },
            CmpOp::Ge  => { self.accumulator.cmp_ge(self.stack.pop()) },
            CmpOp::Ult => { self.accumulator.cmp_ult(self.stack.pop()) },
            CmpOp::Uge => { self.accumulator.cmp_uge(self.stack.pop()) },
        }
    }
    
    //zz All done
}

