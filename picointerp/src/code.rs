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
use super::value::PicoValue;
use super::instruction::{Opcode};

//a PicoCode
//pt PicoCode
/// A picocode value, with mechanisms to break it in to opcode,
/// immediate value, and to get integer values from it as isize or
/// usize
pub trait PicoCode : Clone + Copy + Sized + std::fmt::Debug + std::fmt::Display + PicoValue {
    /// Opcode class for the instruction encoding
    fn opcode_class(self) -> Opcode;
    /// Returns true if the instruction is an immediate operation
    fn code_is_imm(self) -> bool;
    /// Used to retrieve an immediate value - which may be shorter than as_value
    fn code_imm_value(self) -> Self;
    /// Used to retrieve an immediate value as a usize (e.g. stack offset)
    fn code_imm_usize(self) -> usize;
    /// Used when the code element contains e.g. a *pvalue* int
    fn code_as_value(self) -> Self;
    /// Used when the code element is an offset to e.g. the stack
    fn code_as_usize(self) -> usize;
}

//a Label, LabeledInstruction, Encoding
//pt Label
#[derive(Debug)]
pub enum Label {
    None,
    Id(String),
    Offset(isize),
    Address(usize),
}

//ip Label
impl Label {
    //mp as_str
    /// Return a string of the label for assembly/disassembly - perhaps relative to PC in the future
    pub fn as_str(&self) -> String {
        match &self {
            Label::None => {
                String::new()
            },
            Label::Id(s) => {
                format!("{}: ",s)
            },
            Label::Offset(s) => {
                format!("+{}: ",s)
            },
            Label::Address(s) => {
                format!("{} ",s)
            },
        }
    }
    
    //zz All done
}

//pt LabeledInstruction
#[derive(Debug)]
pub struct LabeledInstruction<V:PicoCode> {
    pub label     : Label,
    pub opcode    : Option<Opcode>,
    pub immediate : Option<usize>, // contains IntOp for an Opcode::IntOp
    pub arg1      : Option<V>,
    pub arg2      : Option<V>,
    pub target    : Label,
    pub comment   : Option<String>,
}

//ip LabeledInstruction<V>
impl <V:PicoCode> LabeledInstruction<V> {
    //fp new
    pub fn new() -> Self {
        Self {
            label  : Label::None,
            opcode : None,
            immediate : None,
            arg1 : None,
            arg2 : None,
            target : Label::None,
            comment : None,
        }
    }
    //fp make
    pub fn make(opcode:Opcode, immediate:Option<usize>, arg1:Option<V> ) -> Self {
        Self {
            label  : Label::None,
            opcode : Some(opcode),
            immediate, arg1,
            arg2 : None,
            target : Label::None,
            comment : None,
        }
    }
    //zz All done
}

//pt Encoding
pub trait Encoding<V:PicoCode> {
    //mp to_instruction
    /// Get an instruction from one or more encodings
    fn to_instruction(code:&Vec<V>, ofs:usize) -> Result<(LabeledInstruction<V>, usize),String>;

    //mp of_instruction
    fn of_instruction(inst:&LabeledInstruction<V>) -> Result<Vec<V>,String>;
}

//a isize implementations
//pi PicoCode<isize> for isize
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
    //zz Al done
}

//ip Encoding<isize> for isize {
// Does this work for V:PicoCode instead of isize?
impl Encoding<isize> for isize {
    //fp to_instruction
    fn to_instruction(code:&Vec<isize>, ofs:usize) -> Result<(LabeledInstruction<isize>, usize),String> {
        match code.get(ofs) {
            None => Err(format!("Offset {} outside bounds of code",ofs)),
            Some(v) => {
                let mut instruction = LabeledInstruction::new();
                let opcode  = v.opcode_class();
                let is_imm  = v.code_is_imm();
                let imm     = v.code_imm_usize();
                instruction.opcode = Some(opcode);
                if is_imm {
                    instruction.immediate = Some(imm);
                }
                let num_args = opcode.num_args(is_imm, imm);
                if num_args > 0 {
                    if let Some(data) = code.get(ofs+1) {
                        instruction.arg1 = Some(*data);
                    } else {
                        return Err(format!("Offset {} for first data value is outside bounds of code",ofs+1));
                    }
                }
                if num_args > 1 {
                    if let Some(data) = code.get(ofs+2) {
                        instruction.arg2 = Some(*data);
                    } else {
                        return Err(format!("Offset {} for second data value is outside bounds of code",ofs+2));
                    }
                }
                Ok((instruction, num_args+1))
            }
        }
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
            Ok((v))
        } else {
            Ok((v))
        }
    }

    //zz All done
}

//mt Test for isize
#[cfg(test)]
mod test_isize {
    use super::*;
    use super::super::instruction::IntOp;
    use super::super::heap::PicoHeap;
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
