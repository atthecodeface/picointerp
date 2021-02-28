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

@file    picoinstruction.rs
@brief   Picoinstructio
 */

//a Imports
use super::types::*;

//a Label
//pt Label
/// Used for instructions as target labels and labels for opcodes,
/// essentially prior to assembly and linking
///
/// Not required for general intepretation of code, but in the library
/// to have a common strucuture to support linking.
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

//a Assembler
pub struct Assembler {
}
impl Assembler {
    //mp
    pub fn opcode_str(opcode:Opcode) -> &'static str {
        match opcode {
            Opcode::Const =>             { "cnst" },
            Opcode::PushConst =>         { "pcnst" },
            Opcode::Acc =>               { "acc" },
            Opcode::PushAcc =>           { "pacc" },
            Opcode::EnvAcc =>            { "eacc" },
            Opcode::PushEnvAcc =>        { "peacc" },
            Opcode::OffsetClosure =>     { "offcl" },
            Opcode::PushOffsetClosure => { "poffcl" },
            Opcode::Pop =>               { "pop" },
            Opcode::Assign =>            { "assign" },
            Opcode::ArithOp =>           { "arith" },
            Opcode::LogicOp =>           { "logic" },
            Opcode::IntCmp =>            { "icmp" },
            Opcode::IntBranch =>         { "ibr" },
            Opcode::GetField =>          { "fldget" },
            Opcode::SetField =>          { "fldset" },
            Opcode::MakeBlock =>         { "mkrec" },
            Opcode::Grab =>              { "grab" },
            Opcode::Restart =>           { "rstrt" },
            Opcode::Branch =>            { "br" },
            Opcode::Closure =>           { "clos" },
            Opcode::ClosureRec =>        { "closrec" },
            Opcode::Apply =>             { "app" },
            Opcode::ApplyN =>            { "appn" },
            Opcode::AppTerm =>           { "appterm" },
            Opcode::Return =>            { "ret" },
            Opcode::PushRetAddr =>       { "pushret" },
            Opcode::AddToAcc =>          { "addacc" },
            Opcode::AddToField0 =>       { "addfld" },
            Opcode::IsInt =>             { "isint" },
        }
    }

    pub fn logicop_opcode_str(subop:usize) -> &'static str {
        match LogicOp::of_usize(subop) {
            LogicOp::BoolNot => {"bnot"},
            LogicOp::And     => {"and"},
            LogicOp::Or      => {"or "},
            LogicOp::Xor     => {"xor"},
            LogicOp::Lsl     => {"lsl"},
            LogicOp::Lsr     => {"lsr"},
            LogicOp::Asr     => {"asr"},
        }
    }
    pub fn arithop_opcode_str(subop:usize) -> &'static str {
        match ArithOp::of_usize(subop) {
            ArithOp::Neg    => {"neg"},
            ArithOp::Add    => {"add"},
            ArithOp::Sub    => {"sub"},
            ArithOp::Mul    => {"mul"},
            ArithOp::Div    => {"div"},
            ArithOp::Mod    => {"mod"},
        }
    }
    pub fn cmpop_opcode_str(subop:usize) -> &'static str {
        match CmpOp::of_usize(subop) {
            CmpOp::Eq     => {"cmpeq"},
            CmpOp::Ne     => {"cmpne"},
            CmpOp::Lt     => {"cmplt"},
            CmpOp::Le     => {"cmple"},
            CmpOp::Gt     => {"cmpgt"},
            CmpOp::Ge     => {"cmpge"},
            CmpOp::Ult    => {"cmpult"},
            CmpOp::Uge    => {"cmpuge"},
        }
    }

    pub fn branchop_opcode_str(subop:usize) -> &'static str {
        match BranchOp::of_usize(subop) {
            BranchOp::Eq     => {"beq"},
            BranchOp::Ne     => {"bne"},
            BranchOp::Al     => {"br"},
        }
    }
    
}
//a Instruction
//pt Instruction
#[derive(Debug)]
pub struct Instruction<V:PicoValue> {
    pub opcode    : Opcode,
    pub subop     : Option<usize>,
    pub args      : Vec<V>,
    pub target    : Vec<Label>,
}

//ip Instruction<V>
impl < V:PicoValue> Instruction<V> {
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
    pub fn make(opcode:Opcode, subop:Option<usize>, args:Vec<V> ) -> Self {
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

//pt Encoding
pub trait Encoding<V:PicoValue> : PicoCode {
    /// Used to convert an instruction for a value to a vector of encodings (PicoCode)
    fn of_instruction(inst:&Instruction<V>) -> Result<Vec<Self>,String>;
    //fp to_instruction
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_instruction(code:&Self::Program, ofs:usize) -> Result<(Instruction<V>, usize),String>;
    //fp All done
}

impl <V:PicoValue> Instruction<V> {
    pub fn disassemble_code<C:Encoding<V>>(code:&C::Program, start:usize, end:usize) -> Result<Vec<String>,String> {
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
