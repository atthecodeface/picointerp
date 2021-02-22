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

//a PicoValue - isize with bit 0 set for int, clear for objects
//pi PicoValue for isize
impl PicoValue for isize {
    #[inline]
    /* const */ fn unit() -> Self { 0 }
    #[inline]
    /* const */ fn int(n:isize) -> Self { (n<<1) | 1 }
    #[inline]
    /* const */ fn is_int(self) -> bool { self & 1 == 1 }
    #[inline]
    /* const */ fn is_object(self) -> bool { self & 1 == 0 }
    #[inline]
    /* const */ fn as_isize(self) -> isize { self >> 1 }
    #[inline]
    /* const */ fn as_usize(self) -> usize { (self >> 1) as usize }
    #[inline]
    /* const */ fn as_heap_index(self) -> usize { self as usize }
    #[inline]
    fn negate(self) -> Self          { (! self) ^ 1 }
    #[inline]
    fn add(self, other:Self) -> Self { self + (other-1) }
    #[inline]
    fn sub(self, other:Self) -> Self { self - (other-1) }
    #[inline]
    fn mul(self, other:Self) -> Self { (self>>1) * (other>>1) + 1 }
    #[inline]
    fn div(self, other:Self) -> Self { (self>>1) / (other>>1) }
    #[inline]
    fn rem(self, other:Self) -> Self { (self>>1) % (other>>1) }
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
///  [8]     = 1 for immediate
///  [16;16] = immediate data
impl PicoCode for isize {

    //mp opcode_class
    fn opcode_class(self) -> Opcode {
        num::FromPrimitive::from_isize(self&0xf).unwrap()
    }

    //mp code_is_imm
    fn code_is_imm(self) -> bool {
        self & 0x100 != 0
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
    //fp of_instruction
    fn of_instruction(inst:&LabeledInstruction<isize>) -> Result<Vec<isize>,String> {
        let mut encoding = 0;
        let mut v = Vec::new();
        if let Some(opcode) = inst.opcode {
            encoding += opcode.as_usize() as isize;
            if let Some(immediate) = inst.immediate {
                encoding += (immediate as isize) << 16;
                encoding += 0x100;
            }
            v.push(encoding);
            if let Some(arg) = inst.arg1 {
                v.push(arg);
            }
            if let Some(arg) = inst.arg2 {
                v.push(arg);
            }
            Ok(v)
        } else {
            Ok(v)
        }
    }
    //zz Al done
}

//a PicoHeap - Vec of isize
//ip PicoHeap<isize> for Vec<isize>
impl PicoHeap<isize> for Vec<isize> {
    fn new() -> Self {
        Vec::new()
    }
    #[inline]
    fn alloc_small(&mut self, tag:usize, n:usize) -> isize {
        self.alloc_small(tag, n)
    }
    fn alloc(&mut self, tag:usize, n:usize) -> isize {
        let r = self.len();
        let n = { if n & 1 == 0 {n+1} else {n} };
        self.push( (tag | ((n+1)<<8)) as isize);
        for _ in 0..n {
            self.push(0);
        }
        r as isize
    }
    fn get_field(&self, object:isize, ofs:usize) -> isize {
        let index = (object as usize) + ofs + 1;
        self[index]
    }
}

//a Encoding - use the default
impl Encoding<isize> for isize {
}

//a Test
//mt Test for isize
#[cfg(test)]
mod test_isize {
    use super::*;
    use super::super::types::*;
    use super::super::interpreter::PicoInterp;
    #[test]
    fn test0() {
        let code = vec![0x100]; // Const 0
        assert_eq!( 1, isize::to_instruction(&code, 0).unwrap().1, "Consumes 1 word" );
        assert_eq!( Some(Opcode::Const), isize::to_instruction(&code, 0).unwrap().0.opcode, "Const" );
        assert_eq!( Some(0), isize::to_instruction(&code, 0).unwrap().0.immediate, "immediate 0" );
    }
    fn add_code(code:&mut Vec<isize>, opcode:Opcode, immediate:Option<usize>, arg:Option<isize>) {
        code.append( &mut isize::of_instruction(&LabeledInstruction::make(opcode, immediate, arg)).unwrap());
    }
    #[test]
    fn test1() {
        let mut code = Vec::new();
        add_code(&mut code, Opcode::Const, Some(3), None );
        add_code(&mut code, Opcode::PushConst, Some(2), None );
        add_code(&mut code, Opcode::IntOp, Some(IntOp::Add.as_usize()), None );
        let mut interp = PicoInterp::<isize,Vec<isize>>::new(&code);
        interp.run_code(3);
        assert_eq!(interp.get_accumulator(),isize::int(5));
        
    }
}
