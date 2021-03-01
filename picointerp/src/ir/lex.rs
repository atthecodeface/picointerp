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

@file    lex.rs
@brief   Lexical analyzer for PicoIR assembly
 */

//a Imports
use std::str::Chars;
use super::types::{Token};

//a Lex
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
    pub fn new(text: &'a str) -> Self {
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
                            '-' => {
                                self.start_number(c);
                                self.next_char()
                            },
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
                    if c.is_alphabetic() | c.is_digit(10) | (c == '_') {
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
        test_string(" 1 -2 3  banana 4 5 6", vec![
            Token::Integer(1),
            Token::Integer(-2),
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

