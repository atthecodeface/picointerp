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

@file    interpreter.rs
@brief   Picointerpreter - a small interpreter for a strict evaluation (functional) language
 */

//a Imports
use super::types::*;

//a PicoInterp
//tp PicoExecEnv
/// The environment for a Pico interpreter execution is the PC, the
/// environment chain, and the number of extra arguments at the top of
/// the stack that are not required by the current function (i.e. when
/// this function completes execution and returns by popping the
/// environment stack, the result will be in the accumulator and
/// `extra_args` will be on the stack frame for a further function
/// application
///
/// The extra arguments comes from the approach taken to evaluating
/// multi-argument lambdas; consider an expression
/// ```text
///     f a b c d
/// ```
///
/// The type of f is 'a -> 'b -> 'c-> 'd -> 'e; but f itself might
/// just be a function of two arguments which returns a function of
/// two further arguments, whose result is of type 'e.
/// ```text
///     f : 'a -> 'b -> ( 'c -> 'd -> 'e)
/// ```
///
/// This is indistinguishable from f taking one argument or three arguments.
///
/// One approach to evaluation of this expression is one argument at a
/// time from the left, applying f at each stage. This may (if f takes
/// three arguments, for example) lead to intermediate closures being
/// created.
///
/// The approach taken in ZAIM (and here) is to evaluate all the
/// arguments - from the right - and to push them all on the stack
/// such that the stack consists of [d, c, b, a] - with a on the top.
///
/// f can then be invoked with `extra_args` set to 3; if f is a
/// function of three arguments, then it consumes two of these extra
/// arguments, performs its evaluation, with the result in the
/// accumulator, and leaves the stack with [d] and extra_args set to
/// 1. Presumably (if the expression type-checked okay) the result in
/// the accumulator is a closure, and the return from the evaluation
/// of f actually detects extra_args is now 1, and it invokes the
/// closure with the one argument (i.e. for the invocation, extra_args
/// is 0).
///
/// If f requires more than one argument then it will execute a 'grab
/// N' instruction as its first instruction; this is a magic
/// instruction that checks to see if extra_args is at least N. If it
/// is, then execution continues. If not then a magic closure is
/// created and returned; the magic closure has the address of a
/// Restart instruction *immediately prior to* the grab instruction as
/// its function pointer, and it captures the environment and the
/// *valid* arguments from the stack into this closure, and it returns
/// - effectively it has magically created a curried function
/// closure. When this is invoked later with an argument (or more) the
/// closure runs the Restart instruction, which unpacks the closure
/// onto the stack and the grab instruction will reexecute, but with
/// at least one more argument valid.
///
pub struct PicoExecEnv<V:PicoValue> {
    pc         : usize,
    extra_args : usize,
    env        : V,
}

//ip PicoExecEnv
impl <V:PicoValue> PicoExecEnv<V> {
    fn new(pc:usize, args:usize) -> Self {
        Self { env:V::unit(), pc, extra_args:args-1 }
    }
    //mp add_to_pc
    fn add_to_pc(&mut self, ofs:isize) -> usize{
        self.pc.wrapping_add(ofs as usize)
    }
    //mp stack_pop
    fn stack_pop(&mut self, stack:&mut V::Stack) {
        self.extra_args  = stack.pop().as_usize();
        self.env         = stack.pop();
        self.pc          = stack.pop().as_pc();
    }
    //mp stack_push
    fn stack_push(&self, stack:&mut V::Stack, ret_pc:usize) {
        stack.push(V::of_pc(ret_pc) );
        stack.push(self.env);
        stack.push(V::of_usize(self.extra_args));
    }
    //mp stack_set
    /// Do PushRetAddr of *this* PC
    fn stack_set(&self, stack:&mut V::Stack, ret_pc:usize, stack_ofs:usize) {
        stack.set_relative(stack_ofs+2, V::of_pc(ret_pc) );
        stack.set_relative(stack_ofs+1, self.env);
        stack.set_relative(stack_ofs+0, V::of_usize(self.extra_args));
    }
    //mp jump_to_closure
    fn jump_to_closure<H:PicoHeap<V>>(&mut self, heap:&H, closure:V, extra_args:usize) {
        self.pc          = heap.get_code_val(closure, 0);
        self.env         = closure;
        self.extra_args  = extra_args;
    }
    //mp ret
    fn ret<H:PicoHeap<V>>(&mut self, stack:&mut V::Stack, heap:&H, closure:V) {
        if self.extra_args > 0 {
            let num_args = self.extra_args;
            self.jump_to_closure(heap, closure, num_args-1);
        } else {
            self.stack_pop(stack);
        }
    }

}

//ip Display for PicoExecEnv
impl <V:PicoValue> std::fmt::Display for PicoExecEnv<V> {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} {} {}", self.pc, self.extra_args, &self.env.as_str())
    }
}

//tp PicoInterp
/// A picointerpreter with a reference to the code it has, which then
/// contains its heap and values
pub struct PicoInterp<'a, P:PicoProgram, V:PicoValue, H:PicoHeap<V>> {
    code  : &'a P,
    pub heap  : H,
    pub stack : V::Stack,
    exec_env    : PicoExecEnv<V>,
    accumulator : V,
}

//ip PicoInterp
impl <'a, P:PicoProgram, V:PicoValue, H:PicoHeap<V>> PicoInterp<'a, P, V, H> {

    //fp new
    /// Create a new picointerpreter for a piece of code
    pub fn new(code : &'a P) -> Self {
        let heap        = H::new();
        let stack       = V::Stack::new();
        let exec_env    = PicoExecEnv::new(0,1);
        let accumulator = V::int(0);
        Self { code, heap, stack, exec_env, accumulator }
    }

    //mp set_pc
    pub fn set_pc(&mut self, pc:usize) {
        self.exec_env.pc = pc;
    }

    //mp set_env
    pub fn set_env(&mut self, env:V) {
        self.exec_env.env = env;
    }

    //mp get_env
    pub fn get_env(&mut self) -> V {
        self.exec_env.env
    }

    //mp ret
    pub fn ret(&mut self, frame_size:usize, result:V) {
        self.stack.shrink(frame_size);
        self.accumulator = result;
        self.exec_env.ret(&mut self.stack, &self.heap, self.accumulator);
    }

    //mp get_pc
    pub fn get_pc(&self) -> usize { self.exec_env.pc }

    //mp get_accumulator
    pub fn get_accumulator(&self) -> V { self.accumulator }

    //mp run_code
    pub fn run_code<T:PicoTrace>(&mut self, tracer:&mut T, n:usize) -> PicoExecCompletion {
        for _ in 0..n {
            match self.execute(tracer) {
                PicoExecCompletion::Completed(0) => {
                    return PicoExecCompletion::Completed(0);
                },
                PicoExecCompletion::Completed(_) => {},
                x            => {
                    return x;
                }
            }
        }
        PicoExecCompletion::Completed(n)
    }

    //mi execute
    /// Execute a single instruction
    ///
    /// Only invoked from run_code; this is inlined for speed, and is
    /// really split out here just to make the code easier to read
    #[inline]
    fn execute<T:PicoTrace>(&mut self, tracer:&mut T) -> PicoExecCompletion {
        if tracer.trace_fetch(self.code, self.exec_env.pc) {
            return PicoExecCompletion::Abort(self.exec_env.pc);
        }
        if self.exec_env.pc == usize::MAX {
            return PicoExecCompletion::Completed(0);
        }
        let mut instruction  = self.code.fetch_instruction(self.exec_env.pc);
        match instruction.opcode() {
            Opcode::External => {
                return PicoExecCompletion::External(self.exec_env.pc);
            }
            //cc Const/Acc/Envacc + Push variants
            Opcode::AccessOp => {
                match AccessOp::of_usize(instruction.subop()) {
                    AccessOp::Const => {
                        self.accumulator = V::int(self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0));
                        tracer.trace_exec(|| format!("cnst {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::PushConst => {
                        self.stack.push(self.accumulator);
                        self.accumulator = V::int(self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0));
                        tracer.trace_exec(|| format!("pcnst {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::Acc => {
                        let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                        self.accumulator = self.stack.get_relative(ofs);
                        tracer.trace_exec(|| format!("acc {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::PushAcc => {
                        self.stack.push(self.accumulator);
                        let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                        self.accumulator = self.stack.get_relative(ofs);
                        tracer.trace_exec(|| format!("pacc {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::EnvAcc => {
                        let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                        self.accumulator = self.heap.get_field(self.exec_env.env, ofs);
                        tracer.trace_exec(|| format!("eacc {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::PushEnvAcc => {
                        self.stack.push(self.accumulator);
                        let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                        self.accumulator = self.heap.get_field(self.exec_env.env, ofs);
                        tracer.trace_exec(|| format!("peacc {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::OffsetClosure => { // 0, 2, 4, N - for mutually recursive functions (0 for simply recursive)
                        let value = V::int(self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0));
                        assert_eq!(value.as_usize(), 0);
                        self.accumulator = self.exec_env.env; // + ofs.as_usize();
                        tracer.trace_exec(|| format!("offcl {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                    AccessOp::PushOffsetClosure => {
                        self.stack.push(self.accumulator);
                        let value = V::int(self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0));
                        assert_eq!(value.as_usize(), 0);
                        self.accumulator = self.exec_env.env; // + ofs.as_usize();
                        tracer.trace_exec(|| format!("poffcl {}",&self.accumulator.as_str()));
                        self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                    }
                }
            }
            //cc Pop, Assign
            Opcode::Pop => {
                let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("pop {}",ofs) );
                self.stack.shrink(ofs);
                tracer.trace_stack("Pop", &self.stack, ofs);
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
            }
            Opcode::Assign => {
                let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("assign {} {}",ofs, &self.accumulator.as_str()) );
                self.stack.set_relative(ofs, self.accumulator);
                tracer.trace_stack("Assign", &self.stack, ofs);
                self.accumulator = V::unit();
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
            }
            //cc LogicOp/ArithOp/IntCmp/IntBranch
            Opcode::ArithOp => {
                let int_op = instruction.subop();
                tracer.trace_exec(|| format!("arith {} {} {}", int_op, &self.stack.get_relative(0).as_str(), &self.accumulator.as_str()));
                self.do_arith_op(int_op);
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 0);
            }
            Opcode::LogicOp => {
                let int_op = instruction.subop();
                tracer.trace_exec(|| format!("logic {} {} {}", int_op, &self.stack.get_relative(0).as_str(), &self.accumulator.as_str()));
                self.do_logic_op(int_op);
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 0);
            }
            Opcode::IntCmp => {
                let cmp_op = instruction.subop();
                tracer.trace_exec(|| format!("cmp {} {} {}", cmp_op, &self.stack.get_relative(0).as_str(), &self.accumulator.as_str()));
                self.accumulator = V::int( if self.do_cmp_op(cmp_op & 0xf) {1} else {0} );
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 0);
            }
            Opcode::IntBranch => {
                let cmp_op = instruction.subop();
                // Arg must ALWAYS be fetched
                let ofs = self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("intbr {} {}<>{} ofs {}", cmp_op, &self.stack.get_relative(0).as_str(), &self.accumulator.as_str(), ofs));
                if self.do_cmp_op(cmp_op) {
                    tracer.trace_exec(|| format!("intbr taken"));
                    self.exec_env.pc = self.exec_env.add_to_pc(ofs);
                } else {
                    tracer.trace_exec(|| format!("intbr not taken"));
                    self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                }
            }
            //cc Create record and field access
            Opcode::GetField => {
                let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("fldget {} {}", &self.accumulator.as_str(), ofs));
                self.accumulator = self.heap.get_field(self.accumulator, ofs);
                tracer.trace_exec(|| format!("fldget => {}", &self.accumulator.as_str()));
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
            }
            Opcode::SetField => {
                let ofs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                let data = self.stack.pop();
                self.heap.set_field(self.accumulator, ofs, data);
                tracer.trace_exec(|| format!("fldset {} {} : {}", &self.accumulator.as_str(), ofs, &data.as_str()));
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
            }
            Opcode::MakeBlock => {
                let tag  = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                let size = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 1);
                let record = self.heap.alloc(tag, size);
                self.heap.set_field(record, 0, self.accumulator);
                for i in 1..size {
                    let data = self.stack.pop();
                    self.heap.set_field(record, i, data);
                }
                self.accumulator = record;
                tracer.trace_exec(|| format!("mkrec {} {} => {}", tag, size, self.accumulator.as_str()));
                self.exec_env.pc = self.code.next_pc(&mut instruction, self.exec_env.pc, 2);
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
                let ofs = self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("branch {} {} : {}", self.accumulator.as_str(), taken, ofs));
                if taken {
                    self.exec_env.pc = self.exec_env.add_to_pc(ofs);
                } else {
                    self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                }
            }
            //cc Grab and Restart
            Opcode::Grab => {
                let required_args = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                // extra_args is number of args on the stack on top of the standard 1
                if self.exec_env.extra_args >= required_args {
                    tracer.trace_exec(|| format!("grab (enough) {} {}", required_args, self.exec_env));
                    // Got enough - so we are going to just keep going and use them!
                    self.exec_env.extra_args -= required_args;
                    self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                } else {
                    tracer.trace_exec(|| format!("grab (need more) {} {}", required_args, self.exec_env));
                    let num_args = 1 + self.exec_env.extra_args;
                    self.accumulator = self.heap.alloc_small(PicoTag::Closure.as_usize(), 2+num_args);
                    self.heap.set_code_val(self.accumulator, 0, self.exec_env.pc - P::Code::sizeof_restart());
                    self.heap.set_field(self.accumulator, 1, self.exec_env.env);
                    for i in 0..num_args {
                        let data = self.stack.pop();
                        self.heap.set_field(self.accumulator, i+2, data);
                    }
                    self.exec_env.stack_pop(&mut self.stack);
                }
            }
            Opcode::Restart => {
                let num_args = self.heap.get_record_size(self.exec_env.env) - 2;
                tracer.trace_exec(|| format!("rstrt {} {}", num_args, self.exec_env));
                for i in 0..num_args {
                    self.stack.push( self.heap.get_field(self.exec_env.env, i+2) );
                }
                tracer.trace_stack("Restart", &self.stack, num_args+2);
                self.exec_env.env = self.heap.get_field(self.exec_env.env, 1);
                self.exec_env.extra_args += num_args;
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 0);
            }
            //cc Closures
            Opcode::Closure => {
                let nvars = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                let ofs   = self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 1);
                tracer.trace_exec(|| format!("clos {} {}", nvars, ofs));
                if nvars > 0 { self.stack.push(self.accumulator); }
                self.accumulator = self.heap.alloc_small(PicoTag::Closure.as_usize(), 1+nvars);
                self.heap.set_code_val(self.accumulator, 0, self.exec_env.add_to_pc(ofs));
                for i in 0..nvars {
                    let data = self.stack.pop();
                    self.heap.set_field(self.accumulator, i + 1, data );
                }
                tracer.trace_exec(|| format!("clos => {}", &self.accumulator.as_str()));
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 2);
            }
            Opcode::ClosureRec => {
                let nfuncs = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0); // will be >=1
                let nvars  = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 1); // will be >=1
                let ofs    = self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 2);
                if nvars > 0 { self.stack.push(self.accumulator); }
                self.accumulator = self.heap.alloc_small(PicoTag::Closure.as_usize(), nvars + nfuncs*2 - 1 );
                self.heap.set_code_val(self.accumulator,  0, self.exec_env.add_to_pc(ofs));
                let arg_offset = 1 + ((nfuncs-1) * 2);
                for i in 0..nvars {
                    let data = self.stack.pop();
                    self.heap.set_field(self.accumulator, i + arg_offset, data );
                }
                let rec_offset = 1;
                for i in 0..nfuncs-1 {
                    let ofs    = self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 3+i);
                    let infix_obj = self.heap.set_infix_record(self.accumulator, i*2 + rec_offset, (i*2)+2, self.exec_env.add_to_pc(ofs));
                    self.stack.push(infix_obj);
                }
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, nfuncs+2);
            }
            //cc AddToAcc AddToField0 IsInt
            Opcode::AddToAcc => {
                let value = V::int(self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0));
                self.accumulator = self.accumulator.add(value);
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
            }
            Opcode::IsInt => {
                if !self.accumulator.maybe_int() {
                    self.accumulator = V::int(0);
                } else if self.accumulator.maybe_record() {
                    panic!("Use of IsInt with an heap that cannot tell");
                } else {
                    self.accumulator = V::int(1);
                }
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 0);
            }
            Opcode::AddToField0 => {
                let value = V::int(self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0));
                let mut data = self.heap.get_field(self.accumulator, 0);
                data = data.add(value);
                self.heap.set_field(self.accumulator, 0, data);
                self.accumulator = V::unit();
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
            }
            //cc Function invocation - Apply, AppTerm
            // Apply - does not chain any environment, so this seems to be a tail call
            Opcode::Apply => {
                let num_args = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                self.exec_env.jump_to_closure(&self.heap, self.accumulator, num_args-1);
                tracer.trace_exec(|| format!("app {} => {}", &self.accumulator.as_str(), self.exec_env));
            }
            // ApplyN - chain the current environment, and invoke a function with N arguments
            Opcode::ApplyN => {
                // accumulator = environment to call (with PC at field 0)
                // stack = N arguments (N>=1)
                // replicate N of stack
                // push PC+env+extra_args
                // get pc+env from closure and extra_args = N-1
                // Do Push(arguments)
                let num_args   = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                println!("Apply n {} {} {:?} ",num_args, self.exec_env, self.heap.get_code_val(self.accumulator,0), );
                self.stack.push(V::int(0));
                self.stack.push(V::int(0));
                self.stack.push(V::int(0));
                for i in 0..num_args {
                    self.stack.set_relative(i,self.stack.get_relative(i+3));
                }
                // Do PushRetAddr of *next instruction* PC
                let ret_pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
                self.exec_env.stack_set(&mut self.stack, ret_pc, num_args);
                // Jump to Closure
                self.exec_env.jump_to_closure(&self.heap, self.accumulator, num_args-1);
                tracer.trace_exec(|| format!("appn {} => {}", &self.accumulator.as_str(), self.exec_env));
                tracer.trace_stack("appn", &self.stack, num_args+3);
            }
            Opcode::AppTerm => {
                // accumulator = environment to call (with PC at field 0)
                // stack = N arguments
                // Must pop this stack frame (size provided) which
                // is above the N arguments on the stack!
                let num_args   = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                let frame_size = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 1);
                self.stack.remove_slice(frame_size, num_args);
                // Jump to Closure
                let num_args = self.exec_env.extra_args + num_args;
                self.exec_env.jump_to_closure(&self.heap, self.accumulator, num_args-1);
                tracer.trace_exec(|| format!("appterm {} => {}", &self.accumulator.as_str(), self.exec_env));
                tracer.trace_stack("appn", &self.stack, num_args+3);
            }
            Opcode::Return => {
                // return but there may be more arguments on the stack
                // In this case the accumulator *should* be a closure that can be applied with those arguments
                let frame_size = self.code.arg_as_usize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("ret {} {} => {}", frame_size, &self.accumulator.as_str(), self.exec_env));
                self.stack.shrink(frame_size);
                self.exec_env.ret(&mut self.stack, &self.heap, self.accumulator);
            }
            Opcode::PushRetAddr => {
                let ofs    = self.code.arg_as_isize(&mut instruction, self.exec_env.pc, 0);
                tracer.trace_exec(|| format!("pushret {}", ofs));
                // Do PushRetAddr (PC+ofs)
                let ret_pc = self.exec_env.add_to_pc(ofs);
                self.exec_env.stack_push(&mut self.stack, ret_pc);
                tracer.trace_stack("pushret", &self.stack, 3);
                self.exec_env.pc = self.code.next_pc(&instruction, self.exec_env.pc, 1);
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
        return PicoExecCompletion::Completed(1);
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

