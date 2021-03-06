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

@file    pc_u8.rs
@brief   A packet bytecode representation
 */

//a Imports
use crate::{PicoIRInstruction, PicoIREncoding};
use crate::{PicoCode, PicoProgram};
use crate::base::{Opcode};

//a PicoProgramU8 - array of u8
//pi PicoProgramU8
pub struct PicoProgramU8 {
    pub program : Vec<u8>,
}

//ip PicoProgramU8
impl PicoProgramU8 {
    //mp decode_arg
    /// Fetch the next argument from the PC, and update the PC
    fn decode_arg(&self, code:&mut PicoCodeU8) -> usize {
        let mut r = 0;
        let mut n = 0;
        let upper_bits = !0x7f;
        while n < 64 {
            code.pc += 1;
            let v = self.program[code.pc] as usize;
            r += (v & 0x7f) << n;
            if (v & 0x80) == 0 {
                if (v & 0x40) != 0 {
                    r += upper_bits << n;
                }
                return r;
            }
            n += 7;
        }
        panic!("Unterminated argument in code");
    }

    //fp encode_arg
    /// Encode an argument
    fn encode_arg(mut value:isize ) -> Vec<u8> {
        let mut v = Vec::new();
        loop {
            let r = (value & 0x7f) as u8;
            if (value & !0x7f) == 0 ||
                (value | 0x7f) == -1 {
                v.push(r);
                return v;
            }
            v.push(r | 0x80);
            value = value >> 7;
        }
    }

    //zz All done
}

//ip PicoProgram for PicoProgramU8
impl PicoProgram for PicoProgramU8 {

    //ti Code
    type Code = PicoCodeU8;

    //fp new
    fn new() -> Self {
        Self {program:Vec::new()}
    }

    //fp fetch_instruction
    #[inline]
    fn fetch_instruction(&self, pc:usize) -> PicoCodeU8 {
        PicoCodeU8 { opcode:self.program[pc], pc }
    }

    //mp arg_as_usize - updates code.pc
    /// Used when the code element is an offset to e.g. the stack
    #[inline]
    fn arg_as_usize(&self, code:&mut Self::Code, _pc:usize, _arg:usize, ) -> usize {
        self.decode_arg(code)
    }
    
    //mp arg_as_isize - updates self.pc
    /// Used when the code element is a branch offset
    #[inline]
    fn arg_as_isize(&self, code:&mut Self::Code, _pc:usize, _arg:usize, ) -> isize {
        self.decode_arg(code) as isize
    }

    //mp next_pc - arguments have been consumed *GUARANTEED*
    #[inline]
    fn next_pc(&self, code:&Self::Code, _pc:usize, _num_args:usize) -> usize {
        code.pc+1
    }

    //mp branch_pc
    #[inline]
    fn branch_pc(&self, _code:&Self::Code, pc:usize, ofs:usize) -> usize {
        pc.wrapping_add(ofs)
    }

}
    
//a PicoCodeu8 - u8 code, a PicoCode type
//tp PicoCodeU8 - derive Clone, Copy, Debug required by PicoCode
#[derive(Debug, Clone, Copy)]
pub struct PicoCodeU8 {
    opcode : u8,
    pub(self) pc     : usize,
}

//pi PicoCodeU8
impl PicoCodeU8 {

    //mp code_opcode
    #[inline]
    fn code_opcode(&self) -> usize {
        (self.opcode as usize) & 0x1f
    }

    //fp of_opcode
    #[inline]
    fn of_opcode(opcode:usize) -> Self {
        Self {opcode:opcode as u8, pc:0}
    }

    //mp set_subop
    #[inline]
    fn set_subop(&mut self, subop:usize) {
        self.opcode = self.opcode | ((subop as u8)<<5);
    }

    //mp code_subop
    #[inline]
    fn code_subop(&self) -> usize {
        ((self.opcode as usize) >> 5) & 7
    }

}

//pi std::fmt::Display for PicoCodeU8 required by PicoCode
impl std::fmt::Display for PicoCodeU8 {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:02x}@{}", self.opcode, self.pc)
    }
}

//pi PicoCode for PicoCodeU8
/// This simple implementation for u8 uses
impl PicoCode for PicoCodeU8 {

    //mp opcode
    fn opcode(self) -> Opcode {
        num::FromPrimitive::from_usize(self.code_opcode()).unwrap()
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

//a PicoIREncoding for PicoProgramU8
impl PicoIREncoding for PicoProgramU8 {
    type CodeFragment = Vec<u8>;
    //fp to_pico_ir
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_pico_ir(&self, ofs:usize) -> Result<(PicoIRInstruction, usize),String> {
        let mut v   = self.fetch_instruction(ofs);
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
            for i in 0..num_args {
                instruction.args.push(self.arg_as_isize(&mut v, ofs, i+1));
            }
            let l = self.next_pc(&v, ofs, num_args) - ofs;
            Ok((instruction, l))
        }
    }

    //fp of_pico_ir
    fn of_pico_ir(&self, inst:&PicoIRInstruction, pass:usize, args_remap:&Vec<isize>) -> Result<Self::CodeFragment, String> {
        let mut v = Vec::new();
        let mut encoding = PicoCodeU8::of_opcode(inst.opcode.as_usize());
        if let Some(subop) = inst.subop {
            encoding.set_subop(subop);
        }
        v.push(encoding.opcode);
        for a in args_remap {
            let mut av = Self::encode_arg(*a);
            v.append(&mut av);
        }
        Ok(v)
    }

    //mp add_code_fragment
    fn add_code_fragment(&mut self, mut code_fragment:Self::CodeFragment) -> usize {
        let n = self.program.len();
        self.program.append(&mut code_fragment);
        n
    }
    
    //mp new_code_fragment
    fn new_code_fragment(&self) -> Self::CodeFragment {
        Vec::new()
    }

    //mp append_code_fragment
    fn append_code_fragment(&self, code:&mut Self::CodeFragment, mut fragment:Self::CodeFragment) -> usize {
        let n = code.len();
        code.append(&mut fragment);
        n
    }

    //fp get_code_fragment_pc
    /// Get the PC of the end of the code fragment for branch offset determination
    fn get_code_fragment_pc(&self, code:&Self::CodeFragment) -> usize {
        code.len()
    }
    
    //zz All done
}

//a Test
//mt Test for PicoProgramU8
#[cfg(test)]
mod test_picoprogram_u8 {
    use super::*;
    use crate::base::{Opcode, ArithOp, AccessOp}; //, LogicOp, CmpOp, BranchOp};
    use crate::PicoInterp;
    use crate::PicoValue; //::{PicoInterp};
    use crate::{PicoTraceNone};
    use crate::PicoIRAssembler;
    type Interp<'a> = PicoInterp::<'a,PicoProgramU8,isize, Vec<isize>>;
    fn disassemble_code(program:&PicoProgramU8) {
        println!("{:?}", program.program);
        println!("{:?}", program.disassemble_code(0,program.program.len()));
    }
    #[test]
    fn test0() {
        let mut v = vec![(Opcode::AccessOp.as_usize() as u8), 0]; // Const 0
        let mut code = PicoProgramU8::new();
        code.add_code_fragment(v);
        disassemble_code(&code);
        assert_eq!( 2,                code.to_pico_ir(0).unwrap().1, "Consumes 2 bytes" );
        assert_eq!( Opcode::AccessOp, code.to_pico_ir(0).unwrap().0.opcode, "Const" );
        assert_eq!( 0,                code.to_pico_ir(0).unwrap().0.args[0], "immediate 0" );
    }
    fn add_code(code:&mut PicoProgramU8, opcode:Opcode, subop:Option<usize>, args:Vec<isize>) {
        let inst = PicoIRInstruction::make(opcode, subop, args, vec![]);
        code.add_code_fragment(
            code.of_pico_ir(
                &inst,
                0,
                &inst.args,
            ).unwrap());
    }
    #[test]
    fn test1() {
        let mut code = PicoProgramU8::new();
        add_code(&mut code, Opcode::AccessOp, Some(AccessOp::Const as usize), vec![3]);
        add_code(&mut code, Opcode::AccessOp, Some(AccessOp::PushConst as usize), vec![2]);
        add_code(&mut code, Opcode::ArithOp, Some(ArithOp::Add.as_usize()), vec![] );
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

        let mut code = PicoProgramU8::new();
        code.of_program(&program).unwrap();
        disassemble_code(&code);
        let mut interp = Interp::new(&code);
        let mut trace = PicoTraceNone::new();
        interp.run_code(&mut trace, 3);
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
