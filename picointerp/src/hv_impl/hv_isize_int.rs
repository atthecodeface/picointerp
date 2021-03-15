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

@file    hv_isize_int.rs
@brief   PicoValue and PicoHeap implementation for isize integer values/records
 */

//a Imports
pub use crate::base::{PicoValue, PicoHeap, PicoStack, PicoTag};

//a PicoValue - isize with bit 0 set for int, clear for objects
//pi LocalIsize trait - additional functions for accessing records etc
trait LocalIsize{
    fn infix_hdr(size:usize) -> Self;
    fn record_hdr(tag:usize, size:usize) -> Self;
    fn get_tag(self) -> usize;
    fn get_record_size(self) -> usize;
}

//ip LocalIsize
impl LocalIsize for isize {
    #[inline]
    fn infix_hdr(size:usize) -> Self {
        Self::record_hdr( PicoTag::Infix.as_usize(), size)
    }
    #[inline]
    fn record_hdr(tag:usize, size:usize) -> Self {
        (tag | ((size+1)<<8)) as isize
    }
    #[inline]
    fn get_tag(self) -> usize {
        (self as usize) & 0xff
    }
    #[inline]
    fn get_record_size(self) -> usize {
        ((self as usize >> 8) & 0xffffff)-1
    }
}

//pi PicoStack for isize
pub struct IsizeStack {
    stack:Vec<isize>,
}
impl PicoStack<isize> for IsizeStack {
    fn new() -> Self {
        Self { stack:Vec::new() }
    }

    //mi get_relative
    /// Access the stack relative to the top
    ///
    /// An index of 0 is the top of the stack (i.e. stack.len()-1)
    /// An index of 1 is one value below, and so on
    #[inline]
    fn get_relative(&self, index:usize) -> isize {
        let sp = self.stack.len();
        self.stack[sp-1 - index]
    }

    //mi set_relative
    /// Access the stack relative to the top
    ///
    /// An index of 0 is the top of the stack (i.e. stack.len()-1)
    /// An index of 1 is one value below, and so on
    #[inline]
    fn set_relative(&mut self, index:usize, value:isize) {
        let sp = self.stack.len();
        self.stack[sp-1 - index] = value;
    }

    //mi shrink
    /// Shrink the stack by an amount
    #[inline]
    fn shrink(&mut self, index:usize) {
        let sp = self.stack.len();
        self.stack.truncate(sp - index);
    }

    //mi remove_slice
    /// Remove `amount` words that end `index` words from the top of the stack
    #[inline]
    fn remove_slice(&mut self, index:usize, amount:usize) {
        let sp = self.stack.len();
        let index_to_remove = sp - index;
        for _ in 0..amount {
            self.stack.remove(index_to_remove);
        }
    }

    //mi pop
    /// Pop a value from the stack
    #[inline]
    fn pop(&mut self) -> isize {
        self.stack.pop().unwrap()
    }

    //mi push
    /// Push a value onto the stack
    #[inline]
    fn push(&mut self, value:isize) {
        self.stack.push(value);
    }

    //mi as_str
    /// For trace,
    fn as_str(&self, depth:usize) -> String {
        let n = self.stack.len();
        // format!("{:?}", self.stack.get((n-depth)..(n)).unwrap() )
        format!("{:?}", self.stack.get((0)..(n)).unwrap() )
    }

    //zz All done
}

//pi PicoValue for isize
impl PicoValue for isize {
    type Stack = IsizeStack;
    #[inline]
    fn unit() -> Self { 0 }
    #[inline]
    fn int(n:isize) -> Self { (n<<1) | 1 }
    #[inline]
    fn maybe_int(self)    -> bool { self & 1 == 1 }
    #[inline]
    fn maybe_record(self) -> bool { self & 1 == 0 }
    #[inline]
    fn is_false(self) -> bool { self == 1 }
    #[inline]
    fn as_isize(self) -> isize { self >> 1 }
    #[inline]
    fn as_usize(self) -> usize { (self >> 1) as usize }
    #[inline]
    fn of_usize(value:usize) -> Self { ((value as isize) << 1) | 1 }
    #[inline]
    fn as_pc(self) -> usize { (self >> 1) as usize }
    #[inline]
    fn of_pc(value:usize) -> Self { ((value as isize) << 1) | 1 }
    #[inline]
    fn as_heap_index(self) -> usize { self as usize }

    #[inline]
    fn bool_not(self) -> Self        { if self == 3 {1} else {3} }
    #[inline]
    fn negate(self) -> Self          { (! self) ^ 1 }
    #[inline]
    fn add(self, other:Self) -> Self { self + (other-1) }
    #[inline]
    fn sub(self, other:Self) -> Self { self - (other-1) }
    #[inline]
    fn mul(self, other:Self) -> Self { (((self>>1) * (other>>1)) << 1) + 1 }
    #[inline]
    fn div(self, other:Self) -> Self { (((self>>1) / (other>>1)) << 1) + 1 }
    #[inline]
    fn rem(self, other:Self) -> Self { (((self>>1) % (other>>1)) << 1) + 1 }
    #[inline]
    fn and(self, other:Self) -> Self { self & other }
    #[inline]
    fn or(self, other:Self) -> Self  { self | other }
    #[inline]
    fn xor(self, other:Self) -> Self { (self ^ other) + 1 }
    #[inline]
    fn lsl(self, other:Self) -> Self { ((self-1) << (other>>1)) + 1 }
    #[inline]
    fn lsr(self, other:Self) -> Self { (((self-1) as usize) >> (other>>1)) as isize + 1 }
    #[inline]
    fn asr(self, other:Self) -> Self { ((self-1) >> (other>>1)) + 1 }
    #[inline]
    fn cmp_eq(self, other:Self) -> bool { self == other }
    #[inline]
    fn cmp_ne(self, other:Self) -> bool { self != other }
    #[inline]
    fn cmp_lt(self, other:Self) -> bool { self < other }
    #[inline]
    fn cmp_le(self, other:Self) -> bool { self <= other }
    #[inline]
    fn cmp_gt(self, other:Self) -> bool { self > other }
    #[inline]
    fn cmp_ge(self, other:Self) -> bool { self >= other }
    #[inline]
    fn cmp_ult(self, other:Self) -> bool { (self as usize) <  (other as usize) }
    #[inline]
    fn cmp_uge(self, other:Self) -> bool { (self as usize) >= (other as usize) }

    fn as_str(self) -> String {
        if self.maybe_int() {
            format!("{}", self.as_isize())
        } else {
            format!("obj[{}]", self.as_heap_index())
        }
    }

}

//a PicoHeap - Vec of isize
//ip PicoHeap<isize> for Vec<isize>
impl PicoHeap<isize> for Vec<isize> {
    fn new() -> Self {
        let mut v = Vec::new();
        for _ in 0..64 {
            v.push(0);
        }
        v
    }

    #[inline]
    fn alloc_small(&mut self, tag:usize, n:usize) -> isize {
        self.alloc(tag, n)
    }

    fn alloc(&mut self, tag:usize, n:usize) -> isize {
        let r = self.len();
        self.push( isize::record_hdr(tag,n) );
        let n = { if n & 1 == 0 {n+1} else {n} };
        for _ in 0..n {
            self.push(0);
        }
        r as isize
    }

    #[inline]
    fn get_tag(&self, record:isize)      -> usize {
        let index = record as usize;
        self[index].get_tag()
    }

    #[inline]
    fn get_record_size(&self, record:isize)      -> usize {
        let index = record as usize;
        self[index].get_record_size()
    }

    #[inline]
    fn get_field(&self, record:isize, ofs:usize) -> isize {
        let index = (record as usize) + ofs + 1;
        self[index]
    }

    #[inline]
    fn set_field(&mut self, record:isize, ofs:usize, data:isize) {
        let index = (record as usize) + ofs + 1;
        self[index] = data;
    }

    #[inline]
    fn get_code_val(&self, record:isize, ofs:usize) -> usize {
        let index = (record as usize) + ofs + 1;
        self[index] as usize
    }

    #[inline]
    fn set_code_val(&mut self, record:isize, ofs:usize, data:usize) {
        println!("Set code valu {} {} {:x}", record,ofs,data);
        let index = (record as usize) + ofs + 1;
        self[index] = data as isize;
    }

    #[inline]
    fn set_infix_record(&mut self, record:isize, ofs:usize, size:usize, data:usize) -> isize {
        let index = (record as usize) + ofs + 1;
        self[index]   = isize::infix_hdr(size);
        self[index+1] = data as isize;
        index as isize
    }
}

//a Test
/*
//mt Test for isize
#[cfg(test)]
mod test_isize {
    use super::*;
    // use super::super::types::*;
    use super::super::interpreter::PicoInterp;
    use super::super::pico_ir::{Instruction, Encoding};
    #[test]
    fn test0() {
        let mut code = IsizeProgram::new();
        let mut inst = vec![(1<<12) | (Opcode::Const.as_usize() as isize)];
        code.append( inst ); // Const 0
        println!("{:?}", Instruction::disassemble_code::<isize>(&code, 0, code.len()));
        assert_eq!( 1, isize::to_instruction(&code, 0).unwrap().1, "Consumes 1 word" );
        assert_eq!( Opcode::Const, isize::to_instruction(&code, 0).unwrap().0.opcode, "Const" );
        assert_eq!( isize::int(0), isize::to_instruction(&code, 0).unwrap().0.args[0], "immediate 0" );
    }
    fn add_code(code:&mut IsizeProgram, opcode:Opcode, subop:Option<usize>, args:Vec<isize>) {
        code.append( isize::of_instruction(&Instruction::make(opcode, subop, args)).unwrap());
    }
    #[test]
    fn test1() {
        let mut code = IsizeProgram::new();
        add_code(&mut code, Opcode::Const,     None, vec![3]);
        add_code(&mut code, Opcode::PushConst, None, vec![2]);
        add_code(&mut code, Opcode::ArithOp, Some(ArithOp::Add.as_usize()), vec![] );
        println!("{:?}", Instruction::disassemble_code::<isize>(&code, 0, code.len()));
        let mut interp = PicoInterp::<isize,isize, Vec<isize>>::new(&code);
        interp.run_code(3);
        assert_eq!(interp.get_accumulator(),isize::int(5));
    }
    /*
    #[test]
    fn test2() {
        let mut code = Vec::new();
        let mul_2 = code.len();
        add_code(&mut code, Opcode::Const, Some(10), None, None );
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::Acc, Some(1), None, None );
        add_code(&mut code, Opcode::ArithOp, Some(ArithOp::Mul.as_usize()), None, None );
        add_code(&mut code, Opcode::Return, None, Some(1), None);

        let start = code.len();
        add_code(&mut code, Opcode::Closure,   None, Some(0), Some((mul_2 as isize) - (start as isize)));
        add_code(&mut code, Opcode::MakeBlock, Some(0), Some(1), None); // make block of size 1
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        // top of stack is our 'module'
        add_code(&mut code, Opcode::PushRetAddr, None, Some(7), None); // stack 4 deep, acc = module
        add_code(&mut code, Opcode::Const, Some(20), None, None );   // stack 4 deep, acc = 2 <<2 | 1
        add_code(&mut code, Opcode::PushAcc, Some(4), None, None ); // Push and get our module
        add_code(&mut code, Opcode::GetField, Some(0), None, None ); // Access closure for 'mul'
        add_code(&mut code, Opcode::Apply, None, Some(1), None); // invoke the closure
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        let mut interp = PicoInterp::<isize,Vec<isize>>::new(&code);
        interp.set_pc(start);
        interp.run_code(14);
        assert_eq!(interp.get_accumulator(),isize::int(200));

    }
    #[test]
    fn test3() {
        let mut code = Vec::new();
        add_code(&mut code, Opcode::Restart, None, None, None );

        let fac = code.len();
        add_code(&mut code, Opcode::Grab,    None, Some(1), None ); // Grab 1
        add_code(&mut code, Opcode::Acc, Some(1), None, None );     // Acc 1
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::Const, Some(1), None, None );   // Const 1
        add_code(&mut code, Opcode::IntCmp, Some(CmpOp::Gt.as_usize()), None, None ); // gtint
        let this = code.len();
        let fwd = this+5;
        add_code(&mut code, Opcode::BranchIfNot, None, Some((fwd as isize)-(this as isize)), None ); // branchifnot L6
        add_code(&mut code, Opcode::Acc, Some(0), None, None );     // Acc 0
        add_code(&mut code, Opcode::Return, None, Some(2), None);   // Return 2
        assert_eq!(fwd,  code.len());
        add_code(&mut code, Opcode::Acc, Some(1), None, None );        // Acc 1
        add_code(&mut code, Opcode::OffsetInt, Some(0xfff), None, None );  // OffsetInt -1
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::Acc, Some(2), None, None );     // Acc 2
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::Acc, Some(2), None, None );     // Acc 2
        add_code(&mut code, Opcode::ArithOp, Some(ArithOp::Mul.as_usize()), None, None ); // MulInt
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::OffsetClosure, Some(0), None, None ); // OffsetClosure 0
        add_code(&mut code, Opcode::AppTerm, None, Some(2), Some(4) ); // Appterm 2, 4

        let factorial = code.len();
        add_code(&mut code, Opcode::Acc, Some(0), None, None );     // Acc 0
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::Const, Some(1), None, None );   // Const 1
        add_code(&mut code, Opcode::PushAcc, Some(0), None, None ); // Push
        add_code(&mut code, Opcode::EnvAcc, Some(1), None, None );  // EnvAcc 1
        add_code(&mut code, Opcode::AppTerm, None, Some(2), Some(3) ); // Appterm 2, 3


        let mut interp = PicoInterp::<isize,Vec<isize>>::new(&code);
        interp.stack_push(isize::int(1));
        interp.set_pc(factorial);
        interp.run_code(2);
        assert_eq!(interp.get_accumulator(),isize::int(200));
    }
*/
}
*/
