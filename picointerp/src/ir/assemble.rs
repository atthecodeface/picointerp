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

@file    assemble.rs
@brief   Assembler for PicoIR
 */

//a Imports
use std::collections::HashMap;
use super::types::{Mnem};
use super::parse::{Parser};
use crate::base::{PicoProgram};
use crate::base::{Opcode, ArithOp, LogicOp, CmpOp, BranchOp};

//a Constants
//cc MNEMONICS
const MNEMONICS : [(&str, Opcode, usize);62]= [
    ("cnst",   Opcode::Const, 0),
    ("pcnst",  Opcode::PushConst, 0),
    ("acc",    Opcode::Acc, 0),
    ("pacc",   Opcode::PushAcc, 0),
    ("eacc",   Opcode::EnvAcc, 0),
    ("peacc",  Opcode::PushEnvAcc, 0),
    ("offcl",  Opcode::OffsetClosure, 0),
    ("poffcl", Opcode::PushOffsetClosure, 0),
    ("pop",    Opcode::Pop, 0),
    ("assign", Opcode::Assign, 0),
    ("fldget", Opcode::GetField, 0),
    ("fldset", Opcode::SetField, 0),
    ("mkrec",  Opcode::MakeBlock, 0),
    ("grab",   Opcode::Grab, 0),
    ("rstrt",  Opcode::Restart, 0),
    ("br",     Opcode::Branch, 0),
    ("clos",   Opcode::Closure, 0),
    ("closrec",Opcode::ClosureRec, 0),
    ("app",    Opcode::Apply, 0),
    ("appn",   Opcode::ApplyN, 0),
    ("appterm",Opcode::AppTerm, 0),
    ("ret",    Opcode::Return, 0),
    ("pushret",Opcode::PushRetAddr, 0),
    ("addacc", Opcode::AddToAcc, 0),
    ("addfld", Opcode::AddToField0, 0),
    ("isint",  Opcode::IsInt, 0),

    ("arith",  Opcode::ArithOp, 0),
    ("logic",  Opcode::LogicOp, 0),
    ("icmp",   Opcode::IntCmp, 0),
    ("ibr",    Opcode::IntBranch, 0),

    ("bnot", Opcode::LogicOp,   LogicOp::BoolNot as usize ),
    ("and", Opcode::LogicOp,    LogicOp::And as usize     ),
    ("or ", Opcode::LogicOp,    LogicOp::Or as usize      ),
    ("xor", Opcode::LogicOp,    LogicOp::Xor as usize     ),
    ("lsl", Opcode::LogicOp,    LogicOp::Lsl as usize     ),
    ("lsr", Opcode::LogicOp,    LogicOp::Lsr as usize     ),
    ("asr", Opcode::LogicOp,    LogicOp::Asr as usize     ),

    ("neg", Opcode::ArithOp,    ArithOp::Neg as usize    ),
    ("add", Opcode::ArithOp,    ArithOp::Add as usize    ),
    ("sub", Opcode::ArithOp,    ArithOp::Sub as usize    ),
    ("mul", Opcode::ArithOp,    ArithOp::Mul as usize    ),
    ("div", Opcode::ArithOp,    ArithOp::Div as usize    ),
    ("mod", Opcode::ArithOp,    ArithOp::Mod as usize    ),

    ("cmpeq", Opcode::IntCmp,      CmpOp::Eq as usize     ),
    ("cmpne", Opcode::IntCmp,      CmpOp::Ne as usize     ),
    ("cmplt", Opcode::IntCmp,      CmpOp::Lt as usize     ),
    ("cmple", Opcode::IntCmp,      CmpOp::Le as usize     ),
    ("cmpgt", Opcode::IntCmp,      CmpOp::Gt as usize     ),
    ("cmpge", Opcode::IntCmp,      CmpOp::Ge as usize     ),
    ("cmpult", Opcode::IntCmp,     CmpOp::Ult as usize    ),
    ("cmpuge", Opcode::IntCmp,     CmpOp::Uge as usize    ),

    ("bcmpeq", Opcode::IntBranch,  CmpOp::Eq as usize     ),
    ("bcmpne", Opcode::IntBranch,  CmpOp::Ne as usize     ),
    ("bcmplt", Opcode::IntBranch,  CmpOp::Lt as usize     ),
    ("bcmple", Opcode::IntBranch,  CmpOp::Le as usize     ),
    ("bcmpgt", Opcode::IntBranch,  CmpOp::Gt as usize     ),
    ("bcmpge", Opcode::IntBranch,  CmpOp::Ge as usize     ),
    ("bcmpult", Opcode::IntBranch, CmpOp::Ult as usize    ),
    ("bcmpuge", Opcode::IntBranch, CmpOp::Uge as usize    ),

    ("beq", Opcode::Branch,        BranchOp::Eq as usize     ),
    ("bne", Opcode::Branch,        BranchOp::Ne as usize     ),
    ("br", Opcode::Branch,         BranchOp::Al as usize      ),
];


//a Assembler
//tp Assembler
// #[derive(Debug, Clone, Copy, PartialEq )]
// pub struct OpSubop { o:Opcode, u:usize }
pub type OpSubop = (Opcode, usize);
impl Mnem for OpSubop {}
pub struct Assembler<'a> {
    mnemonic_map:HashMap<&'a str, OpSubop >,
}

//ip Assembler
impl <'a> Assembler<'a> {
    //fp new
    pub fn new() -> Self {
        let mut mnemonic_map = HashMap::new();
        for (mnem,opcode,subop) in &MNEMONICS {
            mnemonic_map.insert(*mnem, (*opcode, *subop) );
        }
        Self { mnemonic_map }
    }

    //fp parse
    pub fn parse(&self, s:&str) {
        let mut p = Parser::new(s, &self.mnemonic_map);
        for t in p {
            println!("{:?}",t);
        }
    }

    //fp opcode_str
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

    //fp logicop_opcode_str
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

    //fp arithop_opcode_str
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

    //fp cmpop_opcode_str
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

    //fp branchop_opcode_str
    pub fn branchop_opcode_str(subop:usize) -> &'static str {
        match BranchOp::of_usize(subop) {
            BranchOp::Eq     => {"beq"},
            BranchOp::Ne     => {"bne"},
            BranchOp::Al     => {"br"},
        }
    }
    
}

//a Test
//mt Test for Assembler
#[cfg(test)]
mod test_assemble {
    use super::{Assembler};
    fn test_string(s:&str) {
        println!("Assemble {}",s);
        let a = Assembler::new();
        a.parse(s);
        // assert!(false);
    }
    #[test]
    fn test0() {
        test_string("; 123\n cnst 0 pcnst 1 grab 3 mkrec 2,3 add sub mul div mod");
    }
}


