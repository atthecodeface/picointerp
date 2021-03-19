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

@file    types.rs
@brief   Part of grammar library
 */

//a Imports
use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::{HashMap, HashSet};

//a Traits
//tt Token
pub trait Token : Sized + Display + Eq + Hash + Copy + Debug {
}

//tt Nonterminal
pub trait Nonterminal : Sized + Display + Eq + Hash + Copy + Debug {
}

//a Element
//tp Element
#[derive(Debug, PartialEq, Clone, Eq, Hash, Copy)]
pub enum Element<N:Nonterminal, T:Token> {
    Token(T),
    Nonterminal(N),
}

//ip Element
impl <N:Nonterminal, T:Token> Element<N,T> {
    pub fn is_token(&self) -> bool {
        match self { Self::Token(_) => true, _ => false }
    }
    pub fn is_nonterminal(&self) -> bool {
        match self { Self::Nonterminal(_) => true, _ => false }
    }
    pub fn borrow_token(&self) -> &T {
        match self { Self::Token(t) => t, _ => {panic!("Cannot borrow token from nonterminal");} }
    }
    pub fn borrow_nonterminal(&self) -> &N {
        match self { Self::Nonterminal(n) => n, _ => {panic!("Cannot borrow nonterminal from token");} }
    }
}

//ip Display for Element
impl <N:Nonterminal, T:Token> std::fmt::Display for Element<N,T> {

    //mp fmt - format for display
    /// Display the element
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Token(t)       => write!(f, "{}", t),
            Self::Nonterminal(n) => write!(f, "{}", n),
        }
    }

    //zz All done
}

