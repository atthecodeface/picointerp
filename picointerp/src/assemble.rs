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
@brief   Assemble picocode from string to 
 */

//a Imports
use regex::Regex;
use super::value::PicoValue;
use super::code::{PicoCode, Label,  Encoding, LabeledInstruction};
use super::instruction::{Opcode, IntOp};

//a Constants
//vi STRING_GET_COMMENT
const STRING_GET_COMMENT : &str = r"^(.*);(.*)$";

//vi STRING_AS_LABELED_ASM - regexp that is true if the string is only whitespace
const STRING_AS_LABELED_ASM : &str = r"^\s*([A-Za-z_][0-9a-zA-Z_]*:|[0-9]+)\s*(.*)$";

//vi STRING_OPCODE - regexp that is true if the string is only whitespace
const STRING_OPCODE : &str = r"^\s*(const|acc|pushconst|pushacc|negint|addint|subint|mulint|divint|modint|andint|orint|xorint|lslint|lsrint|asrintnegint|addint|subint|mulint|divint|modint|andint|orint|xorint|lslint|lsrint|asrint)\s*(.*)$";

//vi STRING_ARG_ID
const STRING_ARG_ID : &str = r"^\s*([A-Za-z_][0-9a-zA-Z_]*)\s*(.*)$";

//vi STRING_ARG_INT
const STRING_ARG_INT : &str = r"^\s*([0-9]+)\s*(.*)$";

//vi Static versions thereof
lazy_static!{
    static ref STRING_GET_COMMENT_REX:     Regex = Regex::new(STRING_GET_COMMENT).unwrap();
    static ref STRING_AS_LABELED_ASM_REX:  Regex = Regex::new(STRING_AS_LABELED_ASM).unwrap();
    static ref STRING_OPCODE_REX:          Regex = Regex::new(STRING_OPCODE).unwrap();
    static ref STRING_ARG_ID_REX:          Regex = Regex::new(STRING_ARG_ID).unwrap();
    static ref STRING_ARG_INT_REX:         Regex = Regex::new(STRING_ARG_INT).unwrap();
}

//a Functions
//pt Assemble
trait Assemble : Sized {
    fn assemble_line(s:&str) -> Result<Self, String>;
    fn disassemble(&self) -> String;
}

//ip Assemble for LabeledInstruction<V> {
impl <V:PicoCode> Assemble for LabeledInstruction<V> {
    //fp assemble_line
    fn assemble_line(line:&str) -> Result<Self, String> {
        let mut instruction = Self::new();
        let s = {
            if let Some(caps) = STRING_GET_COMMENT_REX.captures(line) {
                instruction.comment = Some(caps.get(2).unwrap().as_str().to_string());
                caps.get(1).unwrap().as_str()
            } else {
                line
            }
        };
        let s = {
            if let Some(caps) = STRING_AS_LABELED_ASM_REX.captures(s) {
                instruction.label = Label::Id(caps.get(1).unwrap().as_str().to_string());
                caps.get(2).unwrap().as_str()
            } else {
                s
            }
        };
        let s = {
            if let Some(caps) = STRING_OPCODE_REX.captures(s) {
                let (opcode, opt_n) = {
                    match caps.get(1).unwrap().as_str() {
                        "const"     => (Some(Opcode::Const), None),
                        "acc"       => (Some(Opcode::Acc), None),
                        "pushconst" => (Some(Opcode::PushConst), None),
                        "pushacc"   => (Some(Opcode::PushAcc), None),
                        "negint"    => (Some(Opcode::IntOp), Some(IntOp::Neg)),
                        "addint"    => (Some(Opcode::IntOp), Some(IntOp::Add)),
                        "subint"    => (Some(Opcode::IntOp), Some(IntOp::Sub)),
                        "mulint"    => (Some(Opcode::IntOp), Some(IntOp::Mul)),
                        "divint"    => (Some(Opcode::IntOp), Some(IntOp::Div)),
                        "modint"    => (Some(Opcode::IntOp), Some(IntOp::Mod)),
                        "andint"    => (Some(Opcode::IntOp), Some(IntOp::And)),
                        "orint"     => (Some(Opcode::IntOp), Some(IntOp::Or)),
                        "xorint"    => (Some(Opcode::IntOp), Some(IntOp::Xor)),
                        "lslint"    => (Some(Opcode::IntOp), Some(IntOp::Lsl)),
                        "lsrint"    => (Some(Opcode::IntOp), Some(IntOp::Lsr)),
                        "asrint"    => (Some(Opcode::IntOp), Some(IntOp::Asr)),
                        _ => (None, None),
                    }
                };
                instruction.opcode = opcode;
                if let Some(n) = opt_n {
                    instruction.immediate = Some(n as usize);
                }
                caps.get(2).unwrap().as_str()
            } else {
                s
            }
        };
        let s = {
            if let Some(caps) = STRING_ARG_INT_REX.captures(s) {
                instruction.immediate = Some(caps.get(1).unwrap().as_str().parse().unwrap());
                caps.get(2).unwrap().as_str()
            } else {
                s
            }
        };
        println!("Assembled {} to {:?}", line, instruction);
        Ok(instruction)
    }

    //fp disassemble
    fn disassemble(&self) -> String {
        let mut r = String::new();
        r.push_str(&self.label.as_str());
        match &self.opcode {
            Some(opcode) => {
                let used_immediate =  {
                    match opcode {
                        Opcode::Const => {
                            r.push_str(&format!("const"));
                            false
                        }
                        Opcode::Acc => {
                            r.push_str(&format!("acc"));
                            false
                        }
                        Opcode::PushConst => {
                            r.push_str(&format!("pushconst"));
                            false
                        }
                        Opcode::PushAcc => {
                            r.push_str(&format!("pushacc"));
                            false
                        }
                        Opcode::IntOp => {
                            match IntOp::of_usize(self.immediate.unwrap()).unwrap() {
                                IntOp::Neg => { r.push_str(&format!("negint")); true},
                                IntOp::Add => { r.push_str(&format!("addint")); true},
                                IntOp::Sub => { r.push_str(&format!("subint")); true},
                                IntOp::Mul => { r.push_str(&format!("mulint")); true},
                                IntOp::Div => { r.push_str(&format!("divint")); true},
                                IntOp::Mod => { r.push_str(&format!("modint")); true},
                                IntOp::And => { r.push_str(&format!("andint")); true},
                                IntOp::Or  => { r.push_str(&format!("orint"));  true},
                                IntOp::Xor => { r.push_str(&format!("xorint")); true},
                                IntOp::Lsl => { r.push_str(&format!("lslint")); true},
                                IntOp::Lsr => { r.push_str(&format!("lsrint")); true},
                                IntOp::Asr => { r.push_str(&format!("asrint")); true},
                            }
                        }
                        _ => {
                            r.push_str(&format!("NYI"));
                            false
                        }
                    }
                };
                if !used_immediate {
                    if let Some(immediate) = self.immediate {
                        r.push_str(&format!(" {}",immediate));
                    }
                }
            }
            _ => {},
        }
        if let Some(arg) = self.arg1 {
            r.push_str(&format!(" {}",arg));
        }
        if let Some(arg) = self.arg2 {
            r.push_str(&format!(" {}",arg));
        }
        r
    }

    //zz All done
}

//mt Test for isize
#[cfg(test)]
mod test_isize {
    const SRC : &str = r#"
midpoint:	grab 1
	const 2
	push
	acc 2
	getfield 0
	push
	acc 2
	getfield 0
	addint
	divint
	push
	const 2
	push
	acc 3
	getfield 1
	push
	acc 3
	getfield 1
	addint
	divint
	push
	acc 0
	push
	acc 2
	makeblock 2, 0
	return 4
	restart
mk_point:	grab 1
	acc 1
	push
	acc 1
	makeblock 2, 0
	return 2
    "#;
    use super::*;
    #[test]
    fn test0() {
        let code = vec![0x100]; // Const 0
        let inst = isize::to_instruction(&code, 0).unwrap().0;
        assert_eq!("const 0", inst.disassemble());
    }
    #[test]
    fn test1() {
        for s in SRC.lines() {
            let inst = LabeledInstruction::<isize>::assemble_line(s).unwrap();
            println!( "{}", inst.disassemble() );
        }
        // assert!(false);
    }
}
