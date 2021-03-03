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

@file    pc_u32.rs
@brief   A 32-bit unsigned-integer 'bytecode' representation
 */

//a Imports
use crate::{PicoIRInstruction, PicoIREncoding};
use crate::{PicoCode, PicoProgram, PicoTrace};
use crate::{PicoTraceNone};
use crate::base::{Opcode};

//a LocalU32
//pi LocalU32
trait LocalU32{
    fn as_immediate(isize) -> Option<u32>;
    fn set_immediate(&mut self, imm:u32);
    fn of_opcode(opcode:usize) -> u32;
    fn set_subop(&mut self, subop:usize);
    fn code_subop(self) -> usize;
    fn code_is_imm(self) -> bool;
    fn code_imm_isize(self) -> isize;
    fn code_imm_usize(self) -> usize;
    fn code_as_isize(self) -> isize;
    fn code_as_usize(self) -> usize;
}

//ii LocalU32
impl LocalU32 for u32 {
    //mp of_opcode
    #[inline]
    fn of_opcode(opcode:usize) -> u32{
        opcode as u32
    }

    //mp set_subop
    #[inline]
    fn set_subop(&mut self, subop:usize) {
        *self = *self | ((subop as u32)<<8);
    }

    //mp code_subop
    #[inline]
    fn code_subop(self) -> usize {
        ((self >>8) & 0x7) as usize
    }

    //fp as_immediate
    #[inline]
    fn as_immediate(v:isize) -> Option<u32> {
        if (v >> 15) == 0 || (v >> 15) == -1 {
            Some((v as u32) & 0xffff)
        } else {
            None
        }
    }

    //mp set_immediate
    #[inline]
    fn set_immediate(&mut self, imm:u32) {
        *self = *self | (imm << 16) | 0x1000;
    }

    //mp code_is_imm
    #[inline]
    fn code_is_imm(self) -> bool {
        self & 0x1000 != 0
    }

    //mp code_imm_isize
    // requried for arg_as_isize
    #[inline]
    fn code_imm_isize(self) -> isize {
        ((self as i32) >> 16) as isize
    }

    //mp code_imm_usize
    #[inline]
    fn code_imm_usize(self) -> usize {
        ((self >> 16) & 0xffff) as usize
    }

    //mp code_as_isize
    #[inline]
    fn code_as_isize(self) -> isize {
        (self as i32) as isize
    }
    //mp code_as_usize
    /// sign-extend but keep as unsigned
    #[inline]
    fn code_as_usize(self) -> usize {
        ((self as i32) as isize) as usize
    }
}

//a PicoProgramU32 - a PicoProgram
//pi PicoProgramU32
/// Program32 is a PicoProgram implementation, that uses an array of
/// 32-bit unsigned words to encode the picointerpreter instructions.
/// The words provide an 8-bit opcode/subop and a 16-bit constant
/// field.
///
/// This implementation is optimized to keep the interpreter code size
/// and execution speed high; the length of an instruction is simple
/// to determine from whether it is immediate or not, and the number
/// of arguments it takes. Hence incrementing the PC is simple, and
/// requires no arg-by-arg state maintenance.
///
/// PicoCode density is worse than a true byte-code, although support
/// for 16-bit immediate values is beneficial.
pub struct PicoProgramU32 {
    pub program : Vec<u32>,
}

//ip PicoProgramU32
impl PicoProgramU32 {
    //mp get
    pub fn get(&self, pc:usize) -> Option<u32> {
        match self.program.get(pc) {
            None => None,
            Some(x) => Some(*x),
        }
    }

    //mp fetch
    pub fn fetch(&self, pc:usize) -> u32 {
        self.program[pc]
    }

    //mp len
    pub fn len(&self) -> usize { self.program.len() }

    //mp append
    pub fn append(&mut self, mut code:Vec<u32>) {
        self.program.append(&mut code);
    }

    //zz All done
}

//ip PicoProgram for PicoProgramU32 {
impl PicoProgram for PicoProgramU32 {

    //ti Code
    type Code = u32;

    //fp new
    fn new() -> Self {
        Self {program:Vec::new()}
    }

    //fp fetch_instruction
    #[inline]
    fn fetch_instruction(&self, pc:usize) -> u32 {
        self.program[pc]
    }
    
    //mp arg_as_usize - note not mutating
    /// Used when the code element is an offset to e.g. the stack
    #[inline]
    fn arg_as_usize(&self, code:&mut Self::Code, pc:usize, arg:usize, ) -> usize {
        if code.code_is_imm() {
            if arg == 0 {
                code.code_imm_usize()
            }
            else {
                self.program[pc+arg].code_as_usize()
            }
        } else {
            self.program[pc+arg+1].code_as_usize()
        }
    }

    //mp arg_as_isize - note not mutating
    /// Used when the code element is a branch offset
    #[inline]
    fn arg_as_isize(&self, code:&mut Self::Code, pc:usize, arg:usize, ) -> isize {
        if code.code_is_imm() {
            if arg == 0 {
                code.code_imm_isize()
            }
            else {
                self.program[pc+arg].code_as_isize()
            }
        } else {
            self.program[pc+arg+1].code_as_isize()
        }
    }

    //mp next_pc
    #[inline]
    fn next_pc(&self, code:&Self::Code, pc:usize, num_args:usize) -> usize {
        if code.code_is_imm() {
            pc + num_args
        } else {
            pc + num_args + 1            
        }
    }

    //mp branch_pc
    #[inline]
    fn branch_pc(&self, _code:&Self::Code, pc:usize, ofs:usize) -> usize {
        pc.wrapping_add(ofs)
    }

}
    
//a PicoCode implementation for u32
//pi PicoCode for u32
/// This simple implementation for isize uses:
///  [8;0]   = opcode
///  [4;8]   = subop
///  [12]    = 1 for immediate
///  [16;16] = immediate data
impl PicoCode for u32 {
    //mp opcode
    fn opcode(self) -> Opcode {
        num::FromPrimitive::from_usize((self&0x3f) as usize).unwrap()
    }

    //mp subop
    #[inline]
    fn subop(self) -> usize {
        self.code_subop()
    }

    //fp sizeof_restart
    #[inline]
    fn sizeof_restart() -> usize {1}

    //zz Al done
}

//a PicoIREncoding for PicoProgramU32
impl PicoIREncoding for PicoProgramU32 {
    type CodeFragment = Vec<u32>;
    
    //mp to_instruction
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_instruction(&self, ofs:usize) -> Result<(PicoIRInstruction, usize),String> {
        let mut v = self.fetch_instruction(ofs);
        let opcode  = v.opcode();
        let mut instruction = PicoIRInstruction::new(opcode);
        if opcode.uses_subop() {
            instruction.subop = Some(v.code_subop());
        }
        assert!(opcode != Opcode::ClosureRec);
        let num_args = opcode.num_args();
        if num_args == 0 {
            Ok((instruction, 1))
        } else {
            if v.code_is_imm() {
                instruction.args.push(v.code_imm_isize());
                for i in 1..num_args {
                    instruction.args.push(self.arg_as_isize(&mut v, ofs, i));
                }
                Ok((instruction, num_args))
            } else {
                for i in 0..num_args {
                    instruction.args.push(self.arg_as_isize(&mut v, ofs, i+1));
                }
                Ok((instruction, num_args+1))
            }
        }
    }

    //fp of_instruction
    fn of_instruction(inst:&PicoIRInstruction) -> Result<Vec<u32>,String> {
        let mut v = Vec::new();
        let mut encoding = u32::of_opcode(inst.opcode.as_usize());
        if let Some(subop) = inst.subop {
            encoding.set_subop(subop);
        }
        if inst.args.len()==0 {
            v.push(encoding);
        } else if let Some(imm) = u32::as_immediate(inst.args[0]) {
            encoding.set_immediate(imm);
            v.push(encoding);
            for a in &inst.args[1..] {
                v.push(*a as u32);
            }
        } else {
            v.push(encoding);
            for a in &inst.args {
                v.push(*a as u32);
            }
        }
        Ok(v)
    }

    //mp add_code_fragment
    fn add_code_fragment(&mut self, mut code_fragment:Self::CodeFragment) {
        self.program.append(&mut code_fragment);
    }
}

//a Test
//mt Test for PicoProgramU32
#[cfg(test)]
mod test_picoprogram_u32 {
    use super::*;
    use crate::base::{Opcode, ArithOp, AccessOp}; //, LogicOp, CmpOp, BranchOp};
    use crate::PicoInterp;
    use crate::PicoValue; //::{PicoInterp};
    use crate::PicoIRAssembler;
    type Interp<'a> = PicoInterp::<'a, PicoProgramU32, isize, Vec<isize>>;
    fn disassemble_code(program:&PicoProgramU32) {
        println!("{:?}", program.program);
        println!("{:?}", PicoIRInstruction::disassemble_code::<PicoProgramU32>(program,0,program.program.len()));
    }
    #[test]
    fn test0() {
        let mut code = PicoProgramU32::new();
        let v = vec![(1<<12) | (Opcode::AccessOp.as_usize() as u32)];
        code.add_code_fragment(v);
        disassemble_code(&code);
        assert_eq!( 1,                code.to_instruction(0).unwrap().1, "Consumes 1 word" );
        assert_eq!( Opcode::AccessOp, code.to_instruction(0).unwrap().0.opcode, "Const" );
        assert_eq!( 0,                code.to_instruction(0).unwrap().0.args[0], "immediate 0" );
    }
    fn add_code(code:&mut PicoProgramU32, opcode:Opcode, subop:Option<usize>, args:Vec<isize>) {
        code.add_code_fragment(
            PicoProgramU32::of_instruction(
                &PicoIRInstruction::make(opcode, subop, args)
            ).unwrap());
    }
    #[test]
    fn test1() {
        let mut code = PicoProgramU32::new();
        add_code(&mut code, Opcode::AccessOp, Some(AccessOp::Const as usize), vec![3]);
        add_code(&mut code, Opcode::AccessOp, Some(AccessOp::PushConst as usize), vec![2]);
        add_code(&mut code, Opcode::ArithOp,  Some(ArithOp::Add.as_usize()), vec![] );
        disassemble_code(&code);
        let mut interp = Interp::new(&code);
        let mut trace = PicoTraceNone::new();
        interp.run_code(&mut trace, 3);
        assert_eq!(interp.get_accumulator(),isize::int(5));        
    }
    #[test]
    fn test1b() {
        let s = "cnst 3 pcnst 2 add";
        let mut a = PicoIRAssembler::new();
        let program = a.parse(s).unwrap();
        println!("{}", program.disassemble());

        let mut code = PicoProgramU32::new();
        code.of_program(&program).unwrap();
        disassemble_code(&code);
        let mut interp = Interp::new(&code);
        let mut trace = PicoTraceNone::new();
        interp.run_code(&mut trace, 3);
        assert_eq!(interp.get_accumulator(),isize::int(5));
    }
    #[test]
    fn test2() {
        let mut assem = PicoIRAssembler::new();
        let mut code  = PicoProgramU32::new();

        let mul_2 = code.len();
        code.of_program(&assem.parse("cnst 10 pacc 0 acc 1 mul ret 1").unwrap()).unwrap();
        
        let start = code.len();

        code.of_program(&assem.parse(&format!("clos 0, {} mkrec 0, 1 pacc 0 pushret 7 cnst 20 pacc 4 fldget 0 app 1 pacc 0 pacc 0 pacc 0",(mul_2 as isize)-(start as isize))).unwrap()).unwrap();

        for (i,n) in code.program.iter().enumerate() {
            println!("{} : {:08x}", i, n);
        }
        let mut interp = Interp::new(&code);
        interp.set_pc(start);
        let mut trace = PicoTraceNone::new();
        interp.run_code(&mut trace, 14);
        assert_eq!(interp.get_accumulator(),isize::int(200));

    }
    /*
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
