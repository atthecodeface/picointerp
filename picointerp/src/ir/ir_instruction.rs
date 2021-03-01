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

@file    ir_instruction.rs
@brief   PicoIRInstruction type and implementation
 */

//a Imports
use crate::base::{PicoCode, PicoValue};
use crate::base::{Opcode};
use super::assemble::{Assembler};

//a Label
//pt Label
/// Used for instructions as target labels and labels for opcodes,
/// essentially prior to assembly and linking
///
/// Not required for general intepretation of code, but in the library
/// to have a common strucuture to support linking.
#[derive(Debug)]
pub enum Label {
    Field(String),
    Branch(String),
    Constant(String),
}

//ip Label
impl Label {
    //mp as_str
    /// Return a string of the label for assembly/disassembly - perhaps relative to PC in the future
    pub fn as_str(&self) -> String {
        match &self {
            Label::Field(s) => {
                format!("field:{}: ",s)
            },
            Label::Branch(s) => {
                format!("branch{}: ",s)
            },
            Label::Constant(s) => {
                format!("#{} ",s)
            },
        }
    }
    
    //zz All done
}

//a PicoIRInstruction
//pt PicoIRInstruction
#[derive(Debug)]
pub struct PicoIRInstruction {
    pub opcode    : Opcode,
    pub subop     : Option<usize>,
    pub args      : Vec<isize>,
    pub target    : Vec<Label>,
}

//ip PicoIRInstruction
impl PicoIRInstruction {
    //fp new
    pub fn new(opcode:Opcode) -> Self {
        Self {
            opcode,
            subop  : None,
            args   : Vec::new(),
            target : Vec::new(),
        }
    }

    //fp make
    pub fn make(opcode:Opcode, subop:Option<usize>, args:Vec<isize> ) -> Self {
        Self {
            opcode, subop, args,
            target : Vec::new(),
        }
    }

    //fp disassemble
    pub fn disassemble(&self)  -> String {
        let mut r = Assembler::opcode_str(self.opcode).to_string();
        if let Some(subop) = self.subop {
            match self.opcode {
                Opcode::ArithOp   => { r = Assembler::arithop_opcode_str(subop).to_string(); }
                Opcode::LogicOp   => { r = Assembler::logicop_opcode_str(subop).to_string(); }
                Opcode::IntCmp    => { r = Assembler::cmpop_opcode_str(subop).to_string(); }
                Opcode::IntBranch => { r = format!("b{}",Assembler::cmpop_opcode_str(subop)); }
                _                 => { r = Assembler::branchop_opcode_str(subop).to_string(); }
            }
        }
        for a in &self.args {
            if a.is_int() {
                r.push_str( &format!(" {:?}", a.as_isize()) );
            } else {
                r.push_str( &format!(" obj{:?}", a) );
            }
        }
        r
    }
    //zz All done
}

//pt PicoIREncoding
pub trait PicoIREncoding : PicoCode {
    /// Type of a code fragmet
    type CodeFragment;
    /// Used to convert an instruction for a value to a vector of encodings (PicoCode)
    fn of_instruction(inst:&PicoIRInstruction) -> Result<Self::CodeFragment,String>;
    //fp to_instruction
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_instruction(code:&Self::Program, ofs:usize) -> Result<(PicoIRInstruction, usize),String>;
    //fp All done
}

impl PicoIRInstruction {
    pub fn disassemble_code<C:PicoIREncoding>(code:&C::Program, start:usize, end:usize) -> Result<Vec<String>,String> {
        let mut ptr = start;
        let mut r = Vec::new();
        while ptr < end {
            let (inst, pc_inc) = C::to_instruction(code, ptr)?;
            r.push(inst.disassemble());
            ptr += pc_inc;
        }
        Ok(r)
    }
}
