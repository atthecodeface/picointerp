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
use crate::base::{PicoProgram};
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
                Opcode::AccessOp  => { r = Assembler::accessop_opcode_str(subop).to_string(); }
                _                 => { r = Assembler::branchop_opcode_str(subop).to_string(); }
            }
        }
        for a in &self.args {
            r.push_str( &format!(" {:?}", a) );
        }
        r
    }
    //zz All done
}

//a PicoIRProgram
//pt PicoIRProgram
#[derive(Debug)]
/// The PicoIRProgram represents a program consisting of PicoIRInstructions
pub struct PicoIRProgram {
    pub code      : Vec<PicoIRInstruction>,
    pub labels    : Vec<(String, usize)>,
    // Symbols such as for field offsets? method names?
}

//ip PicoIRProgram
impl PicoIRProgram {
    //fp new
    /// Create a new PicoIRProgram
    pub fn new() -> Self {
        Self {
            code : Vec::new(),
            labels : Vec::new(),
        }
    }

    //mp add_label
    /// Add a new label with the current PC
    pub fn add_label(&mut self, label:String) {
        let pc = self.code.len();
        self.labels.push( (label, pc) );
    }

    //mp add_instruction
    /// Add an instruction at the end of the current code
    pub fn add_instruction(&mut self, inst:PicoIRInstruction) {
        self.code.push(inst);
    }

    //mp resolve
    // pub fn resolve(&mut self, f:FnOnce ) {
    // }

    //mp is_resolved
    /// Determine if the program is fully resolved
    pub fn is_resolved(&mut self) -> bool {
        true
    }
    
    //mp disassemble
    pub fn disassemble(&self)  -> String {
        let mut r = String::new();
        for i in &self.code {
            r.push_str(&i.disassemble());
            r.push_str("\n");
        }
        r
    }

    //zz All done
}

//a PicoIREncoding
//pt PicoIREncoding
/// A trait that adds encoding and decoding a PicoProgram to a PicoIRProgram
pub trait PicoIREncoding : PicoProgram {
    /// Type of a code fragmet
    type CodeFragment;
    /// Used to convert an instruction for a value to a vector of encodings (PicoCode)
    fn of_instruction(inst:&PicoIRInstruction) -> Result<Self::CodeFragment,String>;

    //fp to_instruction
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_instruction(&self, ofs:usize) -> Result<(PicoIRInstruction, usize),String>;

    //fp add_code_fragment
    /// Add a code fragment (created by of_instruction) to a PicoProgram
    fn add_code_fragment(&mut self, code_fragment:Self::CodeFragment);
    
    //fp of_program
    /// A provided method to convert a PicoIRProgram into a PicoProgram
    fn of_program(&mut self, ir_program:&PicoIRProgram) -> Result<(), String> {
        for i in &ir_program.code {
            let code_fragment = Self::of_instruction(i)?;
            self.add_code_fragment(code_fragment);
        }
        Ok(())
    }
}

impl PicoIRInstruction {
    pub fn disassemble_code<P:PicoIREncoding>(program:&P, start:usize, end:usize) -> Result<Vec<String>,String> {
        let mut ptr = start;
        let mut r = Vec::new();
        while ptr < end {
            let (inst, pc_inc) = program.to_instruction(ptr)?;
            r.push(inst.disassemble());
            ptr += pc_inc;
        }
        Ok(r)
    }
}
