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
use std::collections::HashMap;
use std::str::Chars;
use std::io::prelude::Read;
use super::types::*;

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

//a Lex
//tp Token
#[derive(Debug, PartialEq)]
pub enum Token {
    Ident(String),
    Comment(String),
    Integer(isize),
    Char(char),
}

//tp LexState
pub enum LexState {
    Idle,
    Comment,
    Ident,
    Number,
}

//tp Lex
pub struct Lex<'a> {
    chars   : Chars<'a>,
    in_hand : Option<char>,
    state   : LexState,
    string  : String,
}

//ip Lex
impl <'a> Lex<'a> {
    //fp new
    pub fn new(text:&'a str) -> Self {
        // let mut text = Box::new(String::new());
        // buf_reader.read_to_string(&mut text);
        let string = String::new();
        let chars = text.chars();
        let state = LexState::Idle;
        Self { chars, in_hand:None, state, string }
    }

    //mp get_char
    pub fn get_char(&mut self) -> Option<char> {
        if let Some(c) = self.in_hand {
            self.in_hand = None;
            Some(c)
        } else {
            match self.chars.next() {
                None => None,
                Some(c) => Some(c),
            }
        }
    }

    //mp unget_char
    pub fn unget_char(&mut self, c:char) {
        self.in_hand = Some(c);
    }

    //mp skip_whitespace
    /// Return true if more data, false for eof
    pub fn skip_whitespace(&mut self) -> bool {
        loop {
            if let Some(c) = self.get_char() {
                if !c.is_whitespace() {
                    self.unget_char(c);
                    return true;
                }
            } else {
                return false;
            }
        }
    }

    //mp steal_string
    fn steal_string(&mut self) -> String {
        std::mem::replace(&mut self.string, String::new())
    }

    //mp start_number
    fn start_number(&mut self, c:char) {
        self.string.push(c);
        self.state = LexState::Number;
    }

    //mp start_ident
    fn start_ident(&mut self, c:char) {
        self.string.push(c);
        self.state = LexState::Ident;
    }

    //mp start_comment
    fn start_comment(&mut self) {
        self.state = LexState::Comment;
    }

    //mp next_char
    pub fn next_char(&mut self) -> Result<Option<Token>,String> {
        match self.state {
            LexState::Idle => {
                if self.skip_whitespace() {
                    let c = self.get_char().unwrap();
                    if c.is_digit(10) {
                        self.start_number(c);
                        self.next_char()
                    } else if c.is_alphabetic() {
                        self.start_ident(c);
                        self.next_char()
                    } else {
                        match c {
                            ';' =>  {
                                self.start_comment();
                                self.next_char()
                            },
                            ':' => Ok(Some(Token::Char(c))),
                            '#' => Ok(Some(Token::Char(c))),
                            ',' => Ok(Some(Token::Char(c))),
                            _ => Err(format!("Bad character '{}'", c))
                        }
                    }
                } else {
                    Ok(None)
                }
            }
            LexState::Comment => {
                match self.get_char() {
                    None => {
                        self.state = LexState::Idle;
                        Ok(Some(Token::Comment(self.steal_string())))
                    },
                    Some('\n') => {
                        self.state = LexState::Idle;
                        Ok(Some(Token::Comment(self.steal_string())))
                    }
                    Some(c) => {
                        self.string.push(c);
                        self.next_char()
                    }
                }
            }
            LexState::Ident => {
                if let Some(c) = self.get_char() {
                    if ( c.is_alphabetic() |
                         c.is_digit(10) |
                         (c == '_') ) {
                        self.string.push(c);
                        self.next_char()
                    } else {
                        self.unget_char(c);
                        self.state = LexState::Idle;
                        Ok(Some(Token::Ident(self.steal_string())))
                    }
                } else {
                    self.state = LexState::Idle;
                    Ok(Some(Token::Ident(self.steal_string())))
                }
            }
            LexState::Number => {
                if let Some(c) = self.get_char() {
                    if c.is_digit(10) {
                        self.string.push(c);
                        self.next_char()
                    } else {
                        self.unget_char(c);
                        self.state = LexState::Idle;
                        Ok(Some(Token::Integer(self.steal_string().parse::<isize>().unwrap())))
                    }
                } else {
                    self.state = LexState::Idle;
                    Ok(Some(Token::Integer(self.steal_string().parse::<isize>().unwrap())))
                }
            }
        }
    }
    
    //zz All done
}

//ip Iterator for Lex
impl <'a> Iterator for Lex<'a> {
    type Item = Result<Token,String>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.next_char() {
            Err(e)      => Some(Err(e)),
            Ok(Some(x)) => Some(Ok(x)),
            _ => None,
        }
    }
}

//a Test
//mt Test for Lex
#[cfg(test)]
mod test_lex {
    use super::{Lex, Token};
    fn test_string(s:&str, v:Vec<Token>) {
        let t = s.to_string();
        let mut l = Lex::new(&t) ;
        for t in v {
            match l.next() {
                None => panic!("Unexpected end of tokens provided by lex"),
                Some(Err(e)) => panic!("Unexpected error {} from lex", e),
                Some(Ok(t2)) => {
                    assert_eq!(t, t2, "Mismatched token provided lex");
                }
            }
        }
        assert_eq!(l.next(), None, "Lex should have hit end of stream");
    }
    #[test]
    fn test0() {
        test_string("123", vec![Token::Integer(123),
        ]);
        test_string("   123   ", vec![Token::Integer(123),
        ]);
        test_string("   banana", vec![Token::Ident("banana".to_string()),
        ]);
        test_string(" 1 2 3  banana 4 5 6", vec![
            Token::Integer(1),
            Token::Integer(2),
            Token::Integer(3),
            Token::Ident("banana".to_string()),            
            Token::Integer(4),
            Token::Integer(5),
            Token::Integer(6),
        ]);
        test_string(" 1 2 3 ;  banana 4 5 6 \n apple", vec![
            Token::Integer(1),
            Token::Integer(2),
            Token::Integer(3),
            Token::Comment("  banana 4 5 6 ".to_string()),            
            Token::Ident("apple".to_string()),            
        ]);
        test_string(" 1:,  2 3 ;  banana : , 4 5 6 \n: apple,", vec![
            Token::Integer(1),
            Token::Char(':'),
            Token::Char(','),
            Token::Integer(2),
            Token::Integer(3),
            Token::Comment("  banana : , 4 5 6 ".to_string()),            
            Token::Char(':'),
            Token::Ident("apple".to_string()),            
            Token::Char(','),
        ]);
        test_string("a a_ a1", vec![
            Token::Ident("a".to_string()),            
            Token::Ident("a_".to_string()),            
            Token::Ident("a1".to_string()),            
        ]);
    }
}

//a Parser
//tp Parsed
/// Comment |
/// Mnemonic [ ( Ident | Number ) [ , (Ident | Number) ] * ]
/// # Ident
///
/// Fsm:
/// *Idle*  Comment|Mnemonic|Ident
/// # *Label* Ident
/// Mnemonic *Mnemonic* [ ( Ident | Number ) [ , (Ident | Number) ] * ]
/// Mnemonic [ ( Ident | Number ) *Mnemonic_1* [ , *Mnemonic_2* (Ident | Number) ] *Mnemonic_1* * ]
pub trait Mnem : std::fmt::Debug + PartialEq + Copy {}
pub type ParseResult<T:Mnem> = Result<Option<Parsed<T>>,String>;
#[derive(Debug, PartialEq)]
pub enum Parsed<T: Mnem> {
    Comment(String),
    Label(String),
    Mnemonic((T, Vec<Token>)),
    Eof,
}

//tp ParserState
enum ParserState {
    Idle,
    Label,
    Mnemonic,
    Mnemonic_1,
    Mnemonic_2,

}

//tp Parser
pub struct Parser<'a, T:Mnem> {
    mnemonic_map  : &'a HashMap<&'a str, T>,
    lex           : Lex<'a>,
    state         : ParserState,
    token_in_hand : Option<Token>,

    mnemonic      : Option<T>,
    args          : Vec<Token>,
}

//ti Parser
impl <'a, T:Mnem> Parser<'a, T> {
    //fp new
    pub fn new(text:&'a str, mnemonic_map:&'a HashMap<&str, T>) -> Self {
        let lex = Lex::new(text);
        Self { mnemonic_map, lex, state:ParserState::Idle, token_in_hand:None, mnemonic:None, args:Vec::new() }
    }

    //mp take_from_hand
    fn take_from_hand(&mut self) -> Option<Token> {
        std::mem::replace(&mut self.token_in_hand, None)
    }

    //fp reduce
    pub fn reduce(&mut self, opt_token:Option<Token>) -> ParseResult<T> {
        self.token_in_hand = opt_token;
        match &self.state {
            ParserState::Idle => {
                if let Some(t) = self.take_from_hand() {
                    self.handle_token(t)
                } else {
                    Ok(Some(Parsed::Eof))
                }
            },
            ParserState::Mnemonic    |
            ParserState::Mnemonic_1  |
            ParserState::Mnemonic_2  => {
                self.state = ParserState::Idle;
                let args = std::mem::replace(&mut self.args, Vec::new());
                let mnemonic = self.mnemonic.unwrap();
                self.mnemonic = None;
                Ok(Some(Parsed::Mnemonic((mnemonic,args))))
            }
            _ => {
                panic!("Bug - reduce invoked when state was not expecting it");
            }
        }
    }

    //mp handle_token
    pub fn handle_token(&mut self, token:Token) -> ParseResult<T> {
        self.token_in_hand = None;
        match &self.state {
            ParserState::Idle => {
                match token {
                    Token::Comment(s) => Ok(Some(Parsed::Comment(s))),
                    Token::Ident(s)   => {
                        if let Some(ref_t) = self.mnemonic_map.get(s.as_str()) {
                            self.mnemonic = Some(*ref_t);
                            self.state = ParserState::Mnemonic;
                            Ok(None)
                        } else {
                            Err(format!("Unknown mnemonic '{}'", s))
                        }
                    },
                    Token::Char('#')   => {
                        self.state = ParserState::Label;
                        Ok(None)
                    },
                    _ => {
                        Err(format!("Unimmplmented token"))
                    }
                }
            },
            ParserState::Label => {
                match token {
                    Token::Ident(s) => {
                        self.state = ParserState::Idle;
                        Ok(Some(Parsed::Label(s)))
                    }
                    _ => {
                        Err(format!("Expected ident after '#' to define label"))
                    }
                }
            }
            ParserState::Mnemonic => {
                match &token {
                    Token::Ident(s) => {
                        if let Some(ref_t) = self.mnemonic_map.get(s.as_str()) {
                            self.reduce(Some(token))
                        } else {
                            self.args.push(token);
                            self.state = ParserState::Mnemonic_1;
                            Ok(None)
                        }
                    }
                    Token::Integer(_) => {
                        self.args.push(token);
                        self.state = ParserState::Mnemonic_1;
                        Ok(None)
                    }
                    _ => {
                        self.reduce(Some(token))
                    },
                }
            }
            ParserState::Mnemonic_1 => {
                match &token {
                    Token::Char(',') => {
                        self.state = ParserState::Mnemonic_2;
                        Ok(None)
                    },
                    _ => {
                        self.reduce(Some(token))
                    },
                }
            }
            ParserState::Mnemonic_2 => {
                match &token {
                    Token::Ident(s) => {
                        if let Some(ref_t) = self.mnemonic_map.get(s.as_str()) {
                            self.reduce(Some(token))
                        } else {
                            self.args.push(token);
                            self.state = ParserState::Mnemonic_1;
                            Ok(None)
                        }
                    }
                    Token::Integer(_) => {
                        self.args.push(token);
                        self.state = ParserState::Mnemonic_1;
                        Ok(None)
                    }
                    _ => {
                        self.reduce(Some(token))
                    },
                }
            }
            _ => {
                panic!("Bug - handle token invoked on unimplemented state");
            }
        }
    }
    //mp handle_next_token
    pub fn handle_next_token(&mut self) -> ParseResult<T> {
        if let Some(t) = self.take_from_hand() {
            self.handle_token(t)
        } else {
            let opt_t = self.lex.next();
            if opt_t.is_none() {
                self.reduce(None)
            } else {
                match opt_t.unwrap() {
                    Ok(t)  => self.handle_token(t),
                    Err(e) => Err(e),
                }
            }
        }
    }
}

//ip Iterator for Parser
impl <'a, T:Mnem> Iterator for Parser<'a, T> {
    type Item = Result<Parsed<T>,String>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.handle_next_token() {
            Ok(None)    => self.next(),
            Err(e)      => Some(Err(e)),
            Ok(Some(Parsed::Eof))   => None,
            Ok(Some(x)) => Some(Ok(x)),
        }
    }
}

//a Test
//mt Test for Parser
#[cfg(test)]
mod test_parse {
    use super::{Mnem, Parser, Parsed, HashMap, Token};
    impl Mnem for isize {}
    fn test_string(s:&str, v:Vec<Parsed<isize>>) {
        let mut m = HashMap::new();
        m.insert("mnem1", 1);
        let t = s.to_string();
        println!("Parse {}",t);
        let mut p = Parser::new(&t, &m);
        for t in v {
            match p.next() {
                None => panic!("Unexpected end of parser stream provided by parser"),
                Some(Err(e)) => panic!("Unexpected error {} from parser", e),
                Some(Ok(t2)) => {
                    assert_eq!(t, t2, "Mismatched Parse element provided parser");
                }
            }
        }
        assert_eq!(p.next(), None, "Parser should have hit end of stream");
    }
    #[test]
    fn test0() {
        test_string("; 123", vec![Parsed::Comment(" 123".to_string()),
        ]);
        test_string("#a", vec![Parsed::Label("a".to_string()),
        ]);
        test_string("#a #b", vec![Parsed::Label("a".to_string()),
                                  Parsed::Label("b".to_string()),
        ]);
        test_string("#a_2  # b123", vec![Parsed::Label("a_2".to_string()),
                                  Parsed::Label("b123".to_string()),
        ]);
        test_string("#a_2  mnem1", vec![Parsed::Label("a_2".to_string()),
                                        Parsed::Mnemonic((1,vec![])),
        ]);
        test_string("mnem1 #fred", vec![Parsed::Mnemonic((1,vec![])),
                                        Parsed::Label("fred".to_string()),
        ]);
        test_string("mnem1 ;Comment", vec![Parsed::Mnemonic((1,vec![])),
                                           Parsed::Comment("Comment".to_string()),
        ]);
        test_string("mnem1 2", vec![Parsed::Mnemonic((1,vec![Token::Integer(2) ])),
        ]);
        test_string("mnem1 2,3", vec![Parsed::Mnemonic((1,vec![Token::Integer(2), Token::Integer(3) ])),
        ]);
        test_string("mnem1 2,3, #fred", vec![Parsed::Mnemonic((1,vec![Token::Integer(2), Token::Integer(3) ])),
                                             Parsed::Label("fred".to_string()),
        ]);
    }
}

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
        assert!(false);
    }
    #[test]
    fn test0() {
        test_string("; 123\n cnst 0 pcnst 1 grab 3 mkrec 2,3 add sub mul div mod");
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
