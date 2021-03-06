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

@file    parse.rs
@brief   Parser for PicoIR assembler
 */

//a Imports
use std::collections::HashMap;
use super::lex::Lex;
use super::types::{Token};
    
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
/// Mnemonic [ ( Ident | Number ) *Mnemonic1* [ , *Mnemonic2* (Ident | Number) ] *Mnemonic1* * ]
///
pub type ParseResult = Result<Option<Parsed>,String>;
#[derive(Debug, PartialEq)]
pub enum Parsed {
    Comment(String),
    Label(String),
    Mnemonic((String, Vec<Token>)),
    Eof,
}
pub enum ParsedMapped<'a, T> {
    Comment(String),
    Label(String),
    Mnemonic((&'a T, Vec<Token>)),
    Eof,
}
impl <'a, T> ParsedMapped<'a,T> {
    pub fn of(p:Parsed, mnemonic_map:&HashMap<&'a str, &'a T>) -> Self {
        match p {
            Parsed::Comment(s) => Self::Comment(s),
            Parsed::Label(s)   => Self::Label(s),
            Parsed::Eof        => Self::Eof,
            Parsed::Mnemonic((s,args)) => {
                if let Some(t) = mnemonic_map.get(s.as_str()) {
                    Self::Mnemonic((t,args))
                } else {
                    panic!("ParseMapped given a mnemonic to map that was not in the map");
                }
            }
        }
    }
}

//tp ParserState
enum ParserState {
    Idle,
    Label,
    Mnemonic,
    Mnemonic1,
    Mnemonic2,

}

//tp Parser
pub struct Parser {
    keywords      : Vec<String>,
    state         : ParserState,
    token_in_hand : Option<Token>,

    mnemonic      : Option<String>,
    args          : Vec<Token>,
}

//ti Parser
impl Parser {
    //fp new
    pub fn new(keywords:Vec<String>) -> Self {
        Self { keywords, state:ParserState::Idle, token_in_hand:None, mnemonic:None, args:Vec::new() }
    }

    //mp take_from_hand
    fn take_from_hand(&mut self) -> Option<Token> {
        std::mem::replace(&mut self.token_in_hand, None)
    }

    //mi is_keyword
    fn is_keyword(&self, s:&str) -> bool {
        self.keywords.iter().find(|k| s == *k).is_some()
    }

    //fp reduce
    pub fn reduce(&mut self, opt_token:Option<Token>) -> ParseResult {
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
            ParserState::Mnemonic1  |
            ParserState::Mnemonic2  => {
                self.state = ParserState::Idle;
                let args = std::mem::replace(&mut self.args, Vec::new());
                let mnemonic = std::mem::replace(&mut self.mnemonic, None);
                let mnemonic = mnemonic.unwrap();
                Ok(Some(Parsed::Mnemonic((mnemonic,args))))
            }
            _ => {
                panic!("Bug - reduce invoked when state was not expecting it");
            }
        }
    }

    //mp handle_token
    pub fn handle_token(&mut self, token:Token) -> ParseResult {
        self.token_in_hand = None;
        match &self.state {
            ParserState::Idle => {
                match token {
                    Token::Comment(s) => Ok(Some(Parsed::Comment(s))),
                    Token::Ident(s)   => {
                        if self.is_keyword(&s) {
                            self.mnemonic = Some(s);
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
                        Err(format!("Unimplmented token {:?}", token))
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
                        if self.is_keyword(&s) {
                            self.reduce(Some(token))
                        } else {
                            self.args.push(token);
                            self.state = ParserState::Mnemonic1;
                            Ok(None)
                        }
                    }
                    Token::Integer(_) => {
                        self.args.push(token);
                        self.state = ParserState::Mnemonic1;
                        Ok(None)
                    }
                    _ => {
                        self.reduce(Some(token))
                    },
                }
            }
            ParserState::Mnemonic1 => {
                match &token {
                    Token::Char(',') => {
                        self.state = ParserState::Mnemonic2;
                        Ok(None)
                    },
                    _ => {
                        self.reduce(Some(token))
                    },
                }
            }
            ParserState::Mnemonic2 => {
                match &token {
                    Token::Ident(s) => {
                        if self.is_keyword(&s) {
                            self.reduce(Some(token))
                        } else {
                            self.args.push(token);
                            self.state = ParserState::Mnemonic1;
                            Ok(None)
                        }
                    }
                    Token::Integer(_) => {
                        self.args.push(token);
                        self.state = ParserState::Mnemonic1;
                        Ok(None)
                    }
                    _ => {
                        self.reduce(Some(token))
                    },
                }
            }
        }
    }
    //mp handle_next_token
    pub fn handle_next_token(&mut self, lex:&mut impl Iterator<Item = Result<Token,String>>) -> ParseResult {
        if let Some(t) = self.take_from_hand() {
            self.handle_token(t)
        } else {
            let opt_t = lex.next();
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

//tp StringParser
/// Something that borrows the Parser to parse over a particular string
///
/// When the parsing of the string is done, the parser is released.
pub struct StringParser<'b> {
    parser : &'b mut Parser,
    lex    : Lex<'b>,
}
impl <'b> StringParser<'b> {
    pub fn new(parser: &'b mut Parser, text:&'b str) -> Self {
        let lex = Lex::new(text);
        Self { parser, lex }
    }
}
//ip Iterator for StringParser
//
// An iterator for the parser has an Item that has a lifetime of the StringParser,
// since items cannot outlive the StringParser, and the parser itself has a longer lifetime.
impl <'b> Iterator for StringParser<'b> {
    type Item = Result<Parsed,String>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.parser.handle_next_token(&mut self.lex) {
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
    use super::{Parser, StringParser, Parsed, HashMap, Token};
    fn test_string(s:&str, v:Vec<Parsed>) {
        let mut m = HashMap::new();
        m.insert("mnem1", 1);
        let t = s.to_string();
        println!("Parse {}",t);
        let keywords = m.iter().map(|(k,v)| k.to_string()).collect();
        let mut p = Parser::new(keywords);
        let mut sp = StringParser::new(&mut p, &t);
        for t in v {
            match sp.next() {
                None => panic!("Unexpected end of parser stream provided by parser"),
                Some(Err(e)) => panic!("Unexpected error {} from parser", e),
                Some(Ok(t2)) => {
                    assert_eq!(t, t2, "Mismatched Parse element provided parser");
                }
            }
        }
        assert_eq!(sp.next(), None, "Parser should have hit end of stream");
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
                                        Parsed::Mnemonic(("mnem1".to_string(),vec![])),
        ]);
        test_string("mnem1 #fred", vec![Parsed::Mnemonic(("mnem1".to_string(),vec![])),
                                        Parsed::Label("fred".to_string()),
        ]);
        test_string("mnem1 ;Comment", vec![Parsed::Mnemonic(("mnem1".to_string(),vec![])),
                                           Parsed::Comment("Comment".to_string()),
        ]);
        test_string("mnem1 2", vec![Parsed::Mnemonic(("mnem1".to_string(),vec![Token::Integer(2) ])),
        ]);
        test_string("mnem1 2,3", vec![Parsed::Mnemonic(("mnem1".to_string(),vec![Token::Integer(2), Token::Integer(3) ])),
        ]);
        test_string("mnem1 2,3, #fred", vec![Parsed::Mnemonic(("mnem1".to_string(),vec![Token::Integer(2), Token::Integer(3) ])),
                                             Parsed::Label("fred".to_string()),
        ]);
    }
}

