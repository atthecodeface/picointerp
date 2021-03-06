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
use super::types::{Token};
use super::parse::{Parser, StringParser, Parsed};
use crate::ir::{PicoIRInstruction, PicoIRProgram, PicoIRIdentType};
use crate::base::{Opcode, ArithOp, LogicOp, CmpOp, BranchOp, AccessOp};

//a  Arg types an mnemonics
struct Mnemonic {
    mnemonic : String,
    opcode : Opcode,
    subop  : usize,
    arg_types : Vec<PicoIRIdentType>,
}
impl Mnemonic {
    pub fn new(mnemonic:&str, opcode:Opcode, subop:usize, arg_types:&Vec<PicoIRIdentType>) -> Self {
        let arg_types = arg_types.iter().map(|x| *x).collect();
        let mnemonic = mnemonic.to_string();
        Self {mnemonic, opcode, subop, arg_types}
    }
}

//a Constants
//cc MNEMONICS
lazy_static!{
    static ref MNEMONICS : [(&'static str, (Opcode, usize, Vec<PicoIRIdentType>));62] = [
    ("cnst",   (Opcode::AccessOp, AccessOp::Const as usize,              vec![PicoIRIdentType::Integer])),
    ("pcnst",  (Opcode::AccessOp, AccessOp::PushConst as usize,          vec![PicoIRIdentType::Integer])),
    ("acc",    (Opcode::AccessOp, AccessOp::Acc as usize,                vec![PicoIRIdentType::StkAcc])),
    ("pacc",   (Opcode::AccessOp, AccessOp::PushAcc as usize,            vec![PicoIRIdentType::StkAcc])),
    ("eacc",   (Opcode::AccessOp, AccessOp::EnvAcc as usize,             vec![PicoIRIdentType::EnvAcc])),
    ("peacc",  (Opcode::AccessOp, AccessOp::PushEnvAcc as usize,         vec![PicoIRIdentType::EnvAcc])),
    ("offcl",  (Opcode::AccessOp, AccessOp::OffsetClosure as usize,      vec![PicoIRIdentType::OffCl])),
    ("poffcl", (Opcode::AccessOp, AccessOp::PushOffsetClosure as usize,  vec![PicoIRIdentType::OffCl])),

    ("pop",    (Opcode::Pop, 0,                vec![PicoIRIdentType::StkAcc])),
    ("assign", (Opcode::Assign, 0,             vec![PicoIRIdentType::StkAcc])),
    ("fldget", (Opcode::GetField, 0,           vec![PicoIRIdentType::FieldName])),
    ("fldset", (Opcode::SetField, 0,           vec![PicoIRIdentType::FieldName])),
    ("mkrec",  (Opcode::MakeBlock, 0,          vec![PicoIRIdentType::BlkTag, PicoIRIdentType::Integer])),
    ("grab",   (Opcode::Grab, 0,               vec![PicoIRIdentType::Integer])),
    ("rstrt",  (Opcode::Restart, 0,            vec![])),
    ("br",     (Opcode::Branch, 0,             vec![PicoIRIdentType::Branch])),
    ("clos",   (Opcode::Closure, 0,            vec![PicoIRIdentType::Integer, PicoIRIdentType::Branch])),
    ("closrec",(Opcode::ClosureRec, 0,         vec![PicoIRIdentType::Integer, PicoIRIdentType::Branch])), // and more branches
    ("app",    (Opcode::Apply, 0,              vec![PicoIRIdentType::StkAcc])),
    ("appn",   (Opcode::ApplyN, 0,             vec![PicoIRIdentType::StkAcc])),
    ("appterm",(Opcode::AppTerm, 0,            vec![PicoIRIdentType::StkAcc, PicoIRIdentType::StkAcc])),
    ("ret",    (Opcode::Return, 0,             vec![PicoIRIdentType::StkAcc])),
    ("pushret",(Opcode::PushRetAddr, 0,        vec![PicoIRIdentType::Branch])),
    ("addacc", (Opcode::AddToAcc, 0,           vec![PicoIRIdentType::Integer])),
    ("addfld", (Opcode::AddToField0, 0,        vec![PicoIRIdentType::Integer])),
    ("isint",  (Opcode::IsInt, 0,              vec![])),

    ("arith",  (Opcode::ArithOp, 0,            vec![])),
    ("logic",  (Opcode::LogicOp, 0,            vec![])),
    ("icmp",   (Opcode::IntCmp, 0,             vec![])),
    ("ibr",    (Opcode::IntBranch, 0,          vec![])),

    ("bnot", (Opcode::LogicOp,   LogicOp::BoolNot as usize ,                  vec![])),
    ("and", (Opcode::LogicOp,    LogicOp::And as usize     ,                  vec![])),
    ("or ", (Opcode::LogicOp,    LogicOp::Or as usize      ,                  vec![])),
    ("xor", (Opcode::LogicOp,    LogicOp::Xor as usize     ,                  vec![])),
    ("lsl", (Opcode::LogicOp,    LogicOp::Lsl as usize     ,                  vec![])),
    ("lsr", (Opcode::LogicOp,    LogicOp::Lsr as usize     ,                  vec![])),
    ("asr", (Opcode::LogicOp,    LogicOp::Asr as usize     ,                  vec![])),

    ("neg", (Opcode::ArithOp,    ArithOp::Neg as usize    ,                  vec![])),
    ("add", (Opcode::ArithOp,    ArithOp::Add as usize    ,                  vec![])),
    ("sub", (Opcode::ArithOp,    ArithOp::Sub as usize    ,                  vec![])),
    ("mul", (Opcode::ArithOp,    ArithOp::Mul as usize    ,                  vec![])),
    ("div", (Opcode::ArithOp,    ArithOp::Div as usize    ,                  vec![])),
    ("mod", (Opcode::ArithOp,    ArithOp::Mod as usize    ,                  vec![])),

    ("cmpeq", (Opcode::IntCmp,      CmpOp::Eq as usize     ,                  vec![])),
    ("cmpne", (Opcode::IntCmp,      CmpOp::Ne as usize     ,                  vec![])),
    ("cmplt", (Opcode::IntCmp,      CmpOp::Lt as usize     ,                  vec![])),
    ("cmple", (Opcode::IntCmp,      CmpOp::Le as usize     ,                  vec![])),
    ("cmpgt", (Opcode::IntCmp,      CmpOp::Gt as usize     ,                  vec![])),
    ("cmpge", (Opcode::IntCmp,      CmpOp::Ge as usize     ,                  vec![])),
    ("cmpult", (Opcode::IntCmp,     CmpOp::Ult as usize    ,                  vec![])),
    ("cmpuge", (Opcode::IntCmp,     CmpOp::Uge as usize    ,                  vec![])),

    ("bcmpeq", (Opcode::IntBranch,  CmpOp::Eq as usize     ,                  vec![PicoIRIdentType::Branch])),
    ("bcmpne", (Opcode::IntBranch,  CmpOp::Ne as usize     ,                  vec![PicoIRIdentType::Branch])),
    ("bcmplt", (Opcode::IntBranch,  CmpOp::Lt as usize     ,                  vec![PicoIRIdentType::Branch])),
    ("bcmple", (Opcode::IntBranch,  CmpOp::Le as usize     ,                  vec![PicoIRIdentType::Branch])),
    ("bcmpgt", (Opcode::IntBranch,  CmpOp::Gt as usize     ,                  vec![PicoIRIdentType::Branch])),
    ("bcmpge", (Opcode::IntBranch,  CmpOp::Ge as usize     ,                  vec![PicoIRIdentType::Branch])),
    ("bcmpult", (Opcode::IntBranch, CmpOp::Ult as usize    ,                  vec![PicoIRIdentType::Branch])),
    ("bcmpuge", (Opcode::IntBranch, CmpOp::Uge as usize    ,                  vec![PicoIRIdentType::Branch])),

    ("beq", (Opcode::Branch,        BranchOp::Eq as usize   ,                 vec![PicoIRIdentType::Branch])),
    ("bne", (Opcode::Branch,        BranchOp::Ne as usize   ,                 vec![PicoIRIdentType::Branch])),
    ("br", (Opcode::Branch,         BranchOp::Al as usize   ,                 vec![PicoIRIdentType::Branch])),
    ];
}

//a Assembler
//tp Assembler
// #[derive(Debug, Clone, Copy, PartialEq )]
// pub struct OpSubop { o:Opcode, u:usize }
pub type OpSubop = (Opcode, usize, Vec<PicoIRIdentType>);
pub struct Assembler<'a> {
    mnemonic_map  : HashMap<&'a str, Mnemonic>,
    parser        : Parser,
}

//ip Assembler
impl <'a> Assembler<'a> {
    //fp new
    pub fn new() -> Self {
        let mut mnemonic_map = HashMap::new();
        let mut keywords = Vec::new();
        for (mnem,(opcode, subop, arg_types)) in MNEMONICS.iter() {
            keywords.push(mnem.to_string());
            let mnemonic = Mnemonic::new(*mnem, *opcode, *subop, arg_types);
            mnemonic_map.insert(*mnem, mnemonic );
        }
        let parser = Parser::new(keywords);
        Self { mnemonic_map, parser }
    }

    //fp parse
    pub fn parse(&mut self, s:&str) -> Result<PicoIRProgram, String> {
        let mut program = PicoIRProgram::new();
        let sp = StringParser::new(&mut self.parser, s);
        for t in sp {
            let t = t?;
            match t {
                Parsed::Comment(_s) => {
                },
                Parsed::Label(s) => {
                    program.add_label(s);
                },
                Parsed::Mnemonic((mnemonic,token_args)) => {
                    let mnemonic = self.mnemonic_map.get(mnemonic.as_str()).unwrap();
                    let mut args   = Vec::new();
                    let mut idents = Vec::new();
                    let mut i = 0;
                    for t in token_args {
                        match t {
                            Token::Integer(n) => {
                                if i >= mnemonic.arg_types.len() {
                                    return Err(format!("Too many arguments for mnemonic"));
                                }
                                args.push(n);
                                idents.push(None);
                            }
                            Token::Ident(s) => {
                                if i >= mnemonic.arg_types.len() {
                                    return Err(format!("Too many arguments for mnemonic"));
                                }
                                args.push(0);
                                idents.push(Some((mnemonic.arg_types[i], s)));
                            }
                            _ => {
                                return Err(format!("Unexpected token returned to assembler"));
                            }
                        }
                        i += 1;
                    }
                    let opcode = mnemonic.opcode;
                    let subop  = mnemonic.subop;
                    println!("Opcode {:?} subop {:?} expects {} got {}", opcode, subop, opcode.num_args(), args.len());
                    let subop = { if opcode.uses_subop() {Some(subop)} else {None}};
                    let pico_ir = PicoIRInstruction::make(opcode, subop, args, idents);
                    program.add_instruction(pico_ir);
                },
                _ => {}, // Eof, never returned
            }
        }
        Ok(program)
    }

    //fp opcode_str
    pub fn opcode_str(opcode:Opcode) -> &'static str {
        match opcode {
            Opcode::AccessOp =>          { "access" },
            Opcode::External =>          { "extern" },
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
    
    //fp accessop_opcode_str
    pub fn accessop_opcode_str(subop:usize) -> &'static str {
        match AccessOp::of_usize(subop) {
            AccessOp::Const             => {"cnst"},
            AccessOp::PushConst         => {"pcnst"},
            AccessOp::Acc =>               { "acc" },
            AccessOp::PushAcc =>           { "pacc" },
            AccessOp::EnvAcc =>            { "eacc" },
            AccessOp::PushEnvAcc =>        { "peacc" },
            AccessOp::OffsetClosure =>     { "offcl" },
            AccessOp::PushOffsetClosure => { "poffcl" },
        }
    }

    //zz All done
}

//a Test
//mt Test for Assembler
#[cfg(test)]
mod test_assemble {
    use super::{Assembler};
    fn test_string(s:&str) {
        println!("Assemble {}",s);
        let mut a = Assembler::new();
        let program = a.parse(s).unwrap();
        println!("{}", program.disassemble());
        // assert!(false);
    }
    #[test]
    fn test0() {
        test_string("; 123\n cnst 0 pcnst 1 grab 3 mkrec 2,3 add sub mul div mod");
    }
    #[test]
    fn test1() {
        test_string("cnst 1 cnst 1 eacc text  fldget TextElement::magnet app 3");
    }
}


