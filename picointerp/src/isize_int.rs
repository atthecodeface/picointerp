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

@file    code.rs
@brief   Picocode trait and an implementation
 */

//a Imports
use super::types::*;
use super::pico_ir::*;

//a PicoValue - isize with bit 0 set for int, clear for objects
//pi isize - background implementations
trait IsizeLocal{
    fn infix_hdr(size:usize) -> Self;
    fn record_hdr(tag:usize, size:usize) -> Self;
    fn get_tag(self) -> usize;
    fn get_record_size(self) -> usize;
    fn as_immediate(self) -> Option<isize>;
    fn set_immediate(&mut self, imm:isize);
    fn code_subop(self) -> usize;
    fn code_is_imm(self) -> bool;
    fn code_imm_value(self) -> isize;
    fn code_imm_isize(self) -> isize;
    fn code_imm_usize(self) -> usize;
    fn code_as_value(self) -> isize;
    fn code_as_usize(self) -> usize;
}
impl IsizeLocal for isize {
    #[inline]
    fn infix_hdr(size:usize) -> Self {
        Self::record_hdr( Tag::Infix.as_usize(), size)
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

    //mp code_subop
    #[inline]
    fn code_subop(self) -> usize {
        ((self >>8) & 0xf) as usize
    }

    //mp as_immediate
    #[inline]
    fn as_immediate(self) -> Option<isize> {
        if (self >> 15) == 0 || (self >> 15) == -1 {
            Some(self & 0xffff)
        } else {
            None
        }
    }
    fn set_immediate(&mut self, imm:isize) {
        *self = *self | (imm << 16) | 0x1000;
    }

    //mp code_is_imm
    #[inline]
    fn code_is_imm(self) -> bool {
        self & 0x1000 != 0
    }

    //mp code_imm_isize
    fn code_imm_isize(self) -> isize {
        self >> 16
    }

    //mp code_imm_value
    fn code_imm_value(self) -> isize {
        isize::int(self >> 16)
    }

    //mp code_imm_usize
    fn code_imm_usize(self) -> usize {
        ((self >> 16) & 0xffff) as usize
    }
    //mp code_as_value
    fn code_as_value(self) -> isize {
        self
    }
    //mp code_as_usize
    fn code_as_usize(self) -> usize {
        self as usize
    }
}

//pi PicoValue for isize
impl PicoValue for isize {
    #[inline]
    fn unit() -> Self { 0 }
    #[inline]
    fn int(n:isize) -> Self { (n<<1) | 1 }
    #[inline]
    fn is_int(self) -> bool { self & 1 == 1 }
    #[inline]
    fn is_false(self) -> bool { self == 1 }
    #[inline]
    fn is_record(self) -> bool { self & 1 == 0 }
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
}

//a PicoCode - isize
//pi PicoCode for isize
/// This simple implementation for isize uses:
///  [8;0]   = opcode
///  [4;8]   = subop
///  [12]    = 1 for immediate
///  [16;16] = immediate data
impl PicoCode for isize {

    /// Opcode class for the instruction encoding, and amount to increase PC by
    fn opcode_class_and_length(self) -> (Opcode, usize) {
        let opcode = Opcode::of_usize((self&0x3f) as usize);
        let pc_inc = opcode.num_args();
        let pc_inc = {
            if self.code_is_imm() {
                pc_inc
            } else {
                1+pc_inc
            }
        };
        (opcode, pc_inc)
    }

    //mp opcode_class
    fn opcode_class(self) -> Opcode {
        num::FromPrimitive::from_isize(self&0x3f).unwrap()
    }

    //mp subop
    #[inline]
    fn subop(self) -> usize {
        self.code_subop()
    }

    /// Used when the code element is an offset to e.g. the stack
    #[inline]
    fn arg_as_usize(self, pc:usize, arg:usize, code:&Vec<Self>) -> usize {
        if self.code_is_imm() {
            if arg == 0 {
                self.code_imm_usize()
            }
            else {
                code[pc+arg-1] as usize
            }
        } else {
            code[pc+arg] as usize
        }
    }
    
    /// Used when the code element is a branch offset
    #[inline]
    fn arg_as_isize(self, pc:usize, arg:usize, code:&Vec<Self>) -> isize {
        if self.code_is_imm() {
            if arg == 0 {
                self.code_imm_isize()
            }
            else {
                code[pc+arg-1]
            }
        } else {
            code[pc+arg]
        }
    }

    //fp sizeof_restart
    #[inline]
    fn sizeof_restart() -> usize {1}

    //zz Al done
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

//a Encoding
impl Encoding<isize, isize> for isize {
    //fp to_instruction
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_instruction(code:&Vec<isize>, ofs:usize) -> Result<(Instruction<isize>, usize),String> {
        match code.get(ofs) {
            None => Err(format!("Offset {} outside bounds of code",ofs)),
            Some(v) => {
                let opcode  = v.opcode_class();
                let mut instruction = Instruction::new(opcode);
                if opcode.uses_subop() {
                    instruction.subop = Some(v.code_subop());
                }
                assert!(opcode != Opcode::ClosureRec);
                let num_args = opcode.num_args();
                if num_args == 0 {
                    Ok((instruction, 1))
                } else {
                    if v.code_is_imm() {
                        instruction.args.push(v.code_imm_value());
                        for i in 1..num_args {
                            instruction.args.push(code[i])
                        }
                        Ok((instruction, num_args))
                    } else {
                        for i in 0..num_args {
                            instruction.args.push(code[i+1]);
                        }
                        Ok((instruction, num_args+1))
                    }
                }
            }
        }
    }

    //fp of_instruction
    fn of_instruction(inst:&Instruction<isize>) -> Result<Vec<isize>,String> {
        let mut encoding = 0;
        let mut v = Vec::new();
        encoding += inst.opcode.as_usize() as isize;
        if let Some(subop) = inst.subop {
            encoding += (subop as isize) << 8;
        }
        if inst.args.len()==0 {
            v.push(encoding);
        } else if let Some(imm) = inst.args[0].as_immediate() {
            encoding.set_immediate(imm);
            v.push(encoding);
            for a in &inst.args[1..] {
                v.push(*a);
            }
        } else {
            v.push(encoding);
            for a in &inst.args {
                v.push(*a);
            }
        }
        Ok(v)
    }
}

//a Test
//mt Test for isize
#[cfg(test)]
mod test_isize {
    use super::*;
    // use super::super::types::*;
    use super::super::interpreter::PicoInterp;
    use super::super::pico_ir::{Instruction, Encoding};
    #[test]
    fn test0() {
        let code = vec![(1<<12) | (Opcode::Const.as_usize() as isize)]; // Const 0
        println!("{:?}", Instruction::disassemble_code(&code));
        assert_eq!( 1, isize::to_instruction(&code, 0).unwrap().1, "Consumes 1 word" );
        assert_eq!( Opcode::Const, isize::to_instruction(&code, 0).unwrap().0.opcode, "Const" );
        assert_eq!( isize::int(0), isize::to_instruction(&code, 0).unwrap().0.args[0], "immediate 0" );
    }
    fn add_code(code:&mut Vec<isize>, opcode:Opcode, subop:Option<usize>, args:Vec<isize>) {
        code.append( &mut isize::of_instruction(&Instruction::make(opcode, subop, args)).unwrap());
    }
    #[test]
    fn test1() {
        let mut code = Vec::new();
        add_code(&mut code, Opcode::Const,     None, vec![3]);
        add_code(&mut code, Opcode::PushConst, None, vec![2]);
        add_code(&mut code, Opcode::IntOp, Some(IntOp::Add.as_usize()), vec![] );
        println!("{:?}", Instruction::disassemble_code(&code));
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
        add_code(&mut code, Opcode::IntOp, Some(IntOp::Mul.as_usize()), None, None );
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
        add_code(&mut code, Opcode::IntOp, Some(IntOp::Mul.as_usize()), None, None ); // MulInt
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
