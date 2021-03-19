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

@file    rule.rs
@brief   Part of grammar library
 */

//a Imports
use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use super::types::*;

//tp GrammarRule
/// A grammar rule represents a grammar rule such as:
///
/// ```text
/// fred := a b c d
/// ```
///
/// In this case, 'fred' is the nonterminal associated with the
/// rule, and 'a b c d' are tokens or nonterminals that make up
/// the rule
///
/// A grammar rule also has a rule function associated with
/// it.  This is invoked by a parser when the grammar rule is
/// matched (reduced)
///
/// A grammar rule is hence one of the options in a production
///
/// It would be, for example, the right-hand side of
///
///
/// with an associated 'function' to be applied on reduction
///
/// It would then be a vector of three tokens plus the function
#[derive(Debug)]
pub struct GrammarRule<F, N:Nonterminal, T:Token> {
    /// Nonterminal - only used for display
    pub(crate) nonterminal : N,
    /// The rule itself
    pub(crate) rule        : Vec<Element<N,T>>,
    /// Function to invoke on reduction
    pub(crate) rule_fn     : F,
}

//ip GrammarRule
impl <F, N:Nonterminal, T:Token> GrammarRule<F,N,T> {
    //fp new
    pub fn new(nonterminal:N, rule_fn:F) -> Self {
        Self {rule_fn, rule:Vec::new(), nonterminal}
    }
    //cp append_token
    pub fn append_token(mut self, token:T) -> Self {
        self.rule.push(Element::Token(token));
        self
    }
    //cp append_nonterminal
    pub fn append_nonterminal(mut self, nonterminal:N) -> Self {
        self.rule.push(Element::Nonterminal(nonterminal));
        self
    }
    //mp length
    pub fn length(&self) -> usize { self.rule.len() }
    //mp borrow_element
    pub fn borrow_element(&self, posn:usize) -> Option<&Element<N,T>> {
        self.rule.get(posn)
    }
    //mp as_string
    pub fn as_string(&self, marker:usize) -> String {
        let mark_symbol = " @".to_string();
        let mut r = String::new();
        r.push_str( &format!("{} :", self.nonterminal ) );
        for (i,e) in self.rule.iter().enumerate() {
            if i == marker { r.push_str( &mark_symbol ); }
            r.push_str( &format!(" {}",e));
        }
        if marker == self.rule.len() {
            r.push_str( &mark_symbol );
        }
        r
    }
    //mp All done
}

//ip Display for GrammarRule
impl <F, N:Nonterminal, T:Token> std::fmt::Display for GrammarRule<F,N,T> {

    //mp fmt - format for display
    /// Display the rule
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.as_string(9999) )
    }

    //zz All done
}

//tp GrammarRulePos
#[derive(Debug)]
pub struct GrammarRulePos<'a, F, N:Nonterminal, T:Token> {
    /// 'rule' is a grammar production rule
    rule : &'a GrammarRule<F, N, T>,
    /// 'position' is 0 for prior to the first element, 1 for between the first
    /// and second element, and so on.
    position : usize,
}

//ip Display for GrammarRulePos
impl <'a, F, N:Nonterminal, T:Token> std::fmt::Display for GrammarRulePos<'a, F,N,T> {

    //mp fmt - format for display
    /// Display the rule
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.rule.as_string(self.position) )
    }

    //zz All done
}

