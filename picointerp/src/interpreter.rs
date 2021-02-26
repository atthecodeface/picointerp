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

    //mi stack_get_relative
    /// Access the stack relative to the top
    ///
    /// An index of 0 is the top of the stack (i.e. stack.len()-1)
    /// An index of 1 is one value below, and so on
    #[inline]
    fn stack_get_relative(&self, index:usize) -> V {
        let sp = self.stack.len();
        self.stack[sp-1 - index]
    }
    //mi stack_set_relative
    /// Access the stack relative to the top
    ///
    /// An index of 0 is the top of the stack (i.e. stack.len()-1)
    /// An index of 1 is one value below, and so on
    #[inline]
    fn stack_set_relative(&mut self, index:usize, value:V) {
        let sp = self.stack.len();
        self.stack[sp-1 - index] = value;
    }
    //mi stack_shrink
    /// Shrink the stack by an amount
    #[inline]
    fn stack_shrink(&mut self, index:usize) {
        let sp = self.stack.len();
        self.stack.truncate(sp - index);
    }
    //mi stack_remove_slice
    /// Remove `amount` words that end `index` words from the top of the stack
    #[inline]
    fn stack_remove_slice(&mut self, index:usize, amount:usize) {
        let sp = self.stack.len();
        let index_to_remove = sp - index - amount;
        for _ in 0..amount {
            self.stack.remove(index_to_remove);
        }
    }
    //mi stack_pop
    /// Pop a value from the stack
    #[inline]
    fn stack_pop(&mut self) -> V {
        self.stack.pop().unwrap()
    }
    //mi stack_push
    /// Push a value onto the stack
    #[inline]
    pub fn stack_push(&mut self, value:V) {
        self.stack.push(value);
    }
    //mi execute
    #[inline]
    fn execute(&mut self) {
        let pc = self.pc;
        let instruction  = self.code[pc]; // PicoCode
        println!("{}, {:0x?}, {}, {}",pc, instruction, self.stack.len(), self.accumulator);
        let (opcode, pc_inc) = instruction.opcode_class_and_length();
        match opcode {
            //cc Const/Acc/Envacc + Push variants
            Opcode::Const => {
                self.accumulator = self.data_value(instruction);
                self.pc += pc_inc;
            }
            Opcode::PushConst => {
                self.stack_push(self.accumulator);
                self.accumulator = self.data_value(instruction);
                self.pc += pc_inc;
            }
            Opcode::Acc => {
                let ofs = self.data_usize(instruction);
                self.accumulator = self.stack_get_relative(ofs);
                self.pc += pc_inc;
            }
            Opcode::PushAcc => {
                self.stack_push(self.accumulator);
                let ofs = self.data_usize(instruction);
                self.accumulator = self.stack_get_relative(ofs);
                self.pc += pc_inc;
            }
            Opcode::EnvAcc => {
                let ofs = self.data_usize(instruction);
                self.accumulator = self.heap.get_field(self.env, ofs);
                self.pc += pc_inc;
            }
            Opcode::PushEnvAcc => {
                self.stack_push(self.accumulator);
                let ofs = self.data_usize(instruction);
                self.accumulator = self.heap.get_field(self.env, ofs);
                self.pc += pc_inc;
            }
            //cc Pop, Assign
            Opcode::Pop => {
                let ofs = self.data_usize(instruction);
                self.stack_shrink(ofs);
                self.pc += pc_inc;
            }
            Opcode::Assign => {
                let ofs = self.data_usize(instruction);
                self.stack_set_relative(ofs, self.accumulator);
                self.accumulator = V::unit();
                self.pc += pc_inc;
            }
            //cc IntOp/Cmp/Branch
            Opcode::IntOp => {
                let int_op = instruction.code_imm_usize();
                self.do_int_op(int_op & 0xf);
                self.pc += pc_inc;
            }
            Opcode::IntCmp => {
                let cmp_op = instruction.code_imm_usize();
                self.accumulator = V::int( if self.do_cmp_op(cmp_op & 0xf) {1} else {0} );
                self.pc += pc_inc;
            }
            Opcode::IntBranch => {
                let cmp_op = instruction.code_imm_usize();
                if self.do_cmp_op(cmp_op & 0xf) {
                    self.pc = self.code[self.pc-1].code_as_usize();
                } else {
                    self.pc += pc_inc;
                }
            }
            //cc Create record and field access
            Opcode::GetField => {
                let ofs = self.data_usize(instruction);
                self.accumulator = self.heap.get_field(self.accumulator, ofs);
                self.pc += pc_inc;
            }
            Opcode::SetField => {
                let ofs = self.data_usize(instruction);
                let data = self.stack_pop();
                self.heap.set_field(self.accumulator, ofs, data);
                self.pc += pc_inc;
            }
            Opcode::MakeBlock => {
                let tag = instruction.code_imm_usize();
                let size = self.code[self.pc+1].code_as_usize();
                let record = self.heap.alloc(tag, size);
                self.heap.set_field(record, 0, self.accumulator);
                for i in 1..size {
                    let data = self.stack_pop();
                    self.heap.set_field(record, i, data);
                }
                self.accumulator = record;
                self.pc += pc_inc;
            }
            //cc BoolNot and Branch
            Opcode::BoolNot => {
                self.accumulator = self.accumulator.bool_not();
                self.pc += pc_inc;
            }
            Opcode::Branch => {
                let ofs = self.code[self.pc+1].code_as_usize();
                self.pc = self.pc.wrapping_add(ofs);
            }
            Opcode::BranchIf => {
                let ofs = self.code[self.pc+1].code_as_usize();
                if !self.accumulator.is_false() {
                    self.pc = self.pc.wrapping_add(ofs);
                } else {
                    self.pc += pc_inc;
                }
            }
            Opcode::BranchIfNot => {
                let ofs = self.code[self.pc+1].code_as_usize();
                if self.accumulator.is_false() {
                    self.pc = self.pc.wrapping_add(ofs);
                } else {
                    self.pc += pc_inc;
                }
            }
            //cc Grab and Restart - NYI
            Opcode::Grab => {
                self.pc += pc_inc;
                panic!("NYI");
            }/*
    Instruct(RESTART): {
      int num_args = Wosize_val(env) - 2;
      int i;
      sp -= num_args;
      for (i = 0; i < num_args; i++) sp[i] = Field(env, i + 2);
      env = Field(env, 1);
      extra_args += num_args;
      Next;
    }

    Instruct(GRAB): {
      int required = *pc++;
      if (extra_args >= required) {
        extra_args -= required;
      } else {
        mlsize_t num_args, i;
        num_args = 1 + extra_args; /* arg1 + extra args */
        Alloc_small(accu, num_args + 2, Closure_tag);
        Field(accu, 1) = env;
        for (i = 0; i < num_args; i++) Field(accu, i + 2) = sp[i];
        Code_val(accu) = pc - 3; /* Point to the preceding RESTART instr. */
        sp += num_args;
        pc = (code_t)(sp[0]);
        env = sp[1];
        extra_args = Long_val(sp[2]);
        sp += 3;
      }
      Next;
    }*/
            //cc Closures
            Opcode::Closure => {
                let nvars = self.code[self.pc+1].code_as_usize();
                let ofs   = self.code[self.pc+2].code_as_usize();
                println!("Closure of {:x} {:x}",nvars, ofs);
                if nvars > 0 { self.stack_push(self.accumulator); }
                self.accumulator = self.heap.alloc_small(Tag::Closure.as_usize(), 1+nvars);
                self.heap.set_code_val(self.accumulator, 0, self.pc.wrapping_add(ofs));
                self.pc += pc_inc; // should be 2
                for i in 0..nvars {
                    let data = self.stack_pop();
                    self.heap.set_field(self.accumulator, i + 1, data );
                }
            }
            Opcode::ClosureRec => {
                let nfuncs = self.code[self.pc+1].code_as_usize(); // will be >=1
                let nvars  = self.code[self.pc+2].code_as_usize(); // will be >= 1
                let ofs    = self.code[self.pc+3].code_as_usize();
                if nvars > 0 { self.stack_push(self.accumulator); }
                self.accumulator = self.heap.alloc_small(Tag::Closure.as_usize(), nvars + nfuncs*2 - 1 );
                self.heap.set_code_val(self.accumulator,  0, self.pc.wrapping_add(ofs));
                self.pc += pc_inc; // should be 3
                let arg_offset = 1 + ((nfuncs-1) * 2);
                for i in 0..nvars {
                    let data = self.stack_pop();
                    self.heap.set_field(self.accumulator, i + arg_offset, data );
                }
                let rec_offset = 1;
                for i in 0..nfuncs-1 {
                    let ofs = self.code[self.pc].code_as_usize();
                    let infix_obj = self.heap.set_infix_record(self.accumulator, i*2 + rec_offset, (i*2)+2, self.pc.wrapping_add(ofs));
                    self.stack_push(infix_obj);
                    self.pc += 1; 
                }
            }
            //cc Function invocation - Apply, AppTerm
            // Apply
            Opcode::Apply => {
                self.extra_args = self.code[self.pc+1].code_as_usize()-1;
                self.pc = self.heap.get_code_val(self.accumulator, 0);
                self.env = self.accumulator;
                println!("Applied {} {} {}",self.env,self.heap.get_code_val(self.accumulator,0), self.heap.get_code_val(self.accumulator,1), );
            }
            Opcode::ApplyN => {
                // accumulator = environment to call (with PC at field 0)
                // stack = N arguments (N>=1)
                // replicate N of stack
                // push PC+env+extra_args
                // get pc+env from closure and extra_args = N-1
                // Do Push(arguments)
                let num_args = self.data_usize(instruction);
                for _ in 0..num_args {
                    self.stack_push(self.stack_get_relative(num_args-1));
                }
                // Do PushRetAddr of *this* PC
                self.stack_push(V::of_pc(self.pc));
                self.stack_push(self.env);
                self.stack_push(V::of_usize(self.extra_args));
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
                let num_args   = self.code[self.pc+1].code_as_usize();
                let frame_size = self.code[self.pc+2].code_as_usize();
                self.stack_remove_slice(num_args, frame_size);
                // Jump to Closure
                self.pc  = self.heap.get_field(self.accumulator, 0).as_pc();
                self.env = self.accumulator;
                self.extra_args += num_args-1;
            }
            Opcode::AppTermN => {
                // accumulator = environment to call (with PC at field 0)
                // stack = N arguments
                // Must pop this stack frame (size provided) which
                // is above the N arguments on the stack!
                let num_args = self.data_usize(instruction);
                let frame_size = self.code[self.pc+1].code_as_usize();
                self.stack_remove_slice(num_args, frame_size);
                // Jump to Closure
                self.pc  = self.heap.get_field(self.accumulator, 0).as_pc();
                self.env = self.accumulator;
                self.extra_args += num_args-1;
            }
            Opcode::Return => {
                let frame_size = self.code[self.pc+1].code_as_usize();
                self.stack_shrink(frame_size);
                if self.extra_args > 0 { // return but the next argument is there already
                    self.extra_args -= 1;
                    self.pc  = self.heap.get_field(self.accumulator, 0).as_pc();
                    self.env = self.accumulator;
                } else { // return properly
                    self.extra_args  = self.stack_pop().as_usize();
                    self.env         = self.stack_pop();
                    self.pc          = self.stack_pop().as_pc();
                }
            }
            Opcode::PushRetAddr => {
                let ofs    = self.code[self.pc+1].code_as_usize();
                // Do PushRetAddr (PC+ofs)
                self.stack_push(V::of_pc(self.pc.wrapping_add(ofs)));
                self.stack_push(self.env);
                self.stack_push(V::of_usize(self.extra_args));
                self.pc += pc_inc;
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

    //mi data_usize
    #[inline]
    fn data_usize(&self, instruction:V) -> usize {
        if instruction.code_is_imm() {
            instruction.code_imm_usize()
        } else {
            self.code[self.pc+1].code_as_usize()
        }
    }
    
    //mi data_value
    #[inline]
    fn data_value(&self, instruction:V) -> V {
        if instruction.code_is_imm() {
            instruction.code_imm_value()
        } else {
            self.code[self.pc+1].code_as_value()
        }
    }
    
    //mi do_int_op
    #[inline]
    fn do_int_op(&mut self, int_op:usize) {
        match IntOp::of_usize(int_op).unwrap() {
            IntOp::Neg => { self.accumulator = self.accumulator.negate(); },
            IntOp::Add => { self.accumulator = self.accumulator.add(self.stack_pop()); },
            IntOp::Sub => { self.accumulator = self.accumulator.sub(self.stack_pop()); },
            IntOp::Mul => { self.accumulator = self.accumulator.mul(self.stack_pop()); },
            IntOp::Div => { self.accumulator = self.accumulator.div(self.stack_pop()); },
            IntOp::Mod => { self.accumulator = self.accumulator.rem(self.stack_pop()); },
            IntOp::And => { self.accumulator = self.accumulator.and(self.stack_pop()); },
            IntOp::Or  => { self.accumulator = self.accumulator.or (self.stack_pop()); },
            IntOp::Xor => { self.accumulator = self.accumulator.xor(self.stack_pop()); },
            IntOp::Lsl => { self.accumulator = self.accumulator.asr(self.stack_pop()); },
            IntOp::Lsr => { self.accumulator = self.accumulator.lsr(self.stack_pop()); },
            IntOp::Asr => { self.accumulator = self.accumulator.asr(self.stack_pop()); },
            // _ => { self.accumulator = self.accumulator.negate(); },
        }
    }
    
    //mi do_cmp_op
    #[inline]
    fn do_cmp_op(&mut self, cmp_op:usize) -> bool {
        match CmpOp::of_usize(cmp_op).unwrap() {
            CmpOp::Eq  => { self.accumulator.cmp_eq(self.stack_pop()) },
            CmpOp::Ne  => { self.accumulator.cmp_ne(self.stack_pop()) },
            CmpOp::Lt  => { self.accumulator.cmp_lt(self.stack_pop()) },
            CmpOp::Le  => { self.accumulator.cmp_le(self.stack_pop()) },
            CmpOp::Gt  => { self.accumulator.cmp_gt(self.stack_pop()) },
            CmpOp::Ge  => { self.accumulator.cmp_ge(self.stack_pop()) },
            CmpOp::Ult => { self.accumulator.cmp_ult(self.stack_pop()) },
            CmpOp::Uge => { self.accumulator.cmp_uge(self.stack_pop()) },
        }
    }
    
    //zz All done
}

