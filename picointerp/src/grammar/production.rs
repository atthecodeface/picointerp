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

@file    production.rs
@brief   Part of grammar library
 */

//a Imports
use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use super::{Token, Nonterminal, Element, Grammar, GrammarRule};

//tp GrammarProductionTokenIter
pub struct GrammarProductionTokenIter<'a, F, N:Nonterminal, T:Token> {
    production : &'a GrammarProduction<F, N, T>,
    rule : usize,
    token : usize,
}
impl <'a, F, N:Nonterminal, T:Token> Iterator for GrammarProductionTokenIter<'a, F, N, T> {
    type Item = &'a Element<N,T>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.rule >= self.production.rules.len() {
            None
        } else {
            if self.token >= self.production.rules[self.rule].rule.len() {
                self.rule += 1;
                self.token = 0;
                self.next()
            } else {
                self.token += 1;
                Some(&self.production.rules[self.rule].rule[self.token-1])
            }
        }
    }
}
//tp GrammarProduction
/// A list of grammar_rule instances
///
/// This structure owns the grammar_rules.
/// Productions are created from rules.
#[derive(Debug)]
pub struct GrammarProduction<F, N:Nonterminal, T:Token> {
    pub(crate) nonterminal : N,
    pub(crate) rules       : Vec<GrammarRule<F,N,T>>,
    pub(crate) initial_tokens : Vec<T>,
    /// The follow_set for a nonterminal is the set of tokens that
    /// *may* come after this production legally in the grammar. This
    /// can be used to handle reduce-reduce conflicts using lookahead
    /// - if the lookahead token is *not* in the follow_set, then this
    /// reduction is *not* permitted - but a different reduction may
    /// be
    pub(crate) follow_set : Vec<T>,
}

//ip GrammarProduction
impl <F, N:Nonterminal, T:Token> GrammarProduction<F, N, T> {
    //fp new
    /// Create a new production for a nonterminal, with no rules
    pub fn new(nonterminal:N) -> Self {
        let rules = Vec::new();
        let initial_tokens = Vec::new();
        let follow_set = Vec::new();
        Self { nonterminal, rules, initial_tokens, follow_set }
    }
    //cp add_rule
    /// Add a rule to the production
    pub fn add_rule(mut self, rule:GrammarRule<F,N,T>) -> Self {
        self.rules.push(rule);
        self
    }
    //mp borrow_initial_tokens
    /// Borrow the initial tokens vector
    pub fn borrow_initial_tokens(&self) -> &Vec<T> {
        &self.initial_tokens
    }
    //mp iter_elements
    pub fn iter_elements<'a> (&'a self) -> impl Iterator<Item = &Element<N,T>> {
        GrammarProductionTokenIter { production:self, rule:0, token:0 }
    }
    //mp find_initial_tokens
    /// Find the initial tokens that this production may have, based
    /// on its current set and its rules
    ///
    /// Return None if the current initial set is complete; Some()
    /// with a larger set than currently if more initial tokens were
    /// found
    pub fn find_initial_tokens(&self, productions:&Vec<GrammarProduction<F,N,T>>) -> Option<Vec<T>> {
        let mut changed = false;
        let mut new_initial_tokens = Vec::new();
        for t in &self.initial_tokens { new_initial_tokens.push(*t); }
        for r in &self.rules {
            let e = r.borrow_element(0).unwrap();
            if e.is_token() {
                let t = e.borrow_token();
                if !new_initial_tokens.contains(t) {
                    new_initial_tokens.push(*t);
                    changed = true;
                }
            } else {
                let n = e.borrow_nonterminal();
                for p in productions {
                    if p.nonterminal == *n {
                        for t in &p.initial_tokens {
                            if !new_initial_tokens.contains(t) {
                                new_initial_tokens.push(*t);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        if changed { Some(new_initial_tokens)} else {None}
    }
    //mp find_next_tokens_of_rule_position
    /// This is invoked for a rule _ : a b . c d, where b is this
    /// production, to determine the set of legal tokens that may
    /// follow a nonterminal
    ///
    /// In parsing a sentence with this grammar if a token *not* in
    /// the legal set is found then a reduction will be required.
    fn find_next_tokens_of_rule_position(&self, grammar:&Grammar<F,N,T>, rule:&GrammarRule<F,N,T>, position:usize, token_set:&mut Vec<T> ) -> bool {
        let mut changed = false;
        match rule.borrow_element(position) {
            Some(Element::Token(t)) => {
                if !token_set.contains(t) { token_set.push(*t); changed=true; }
            },
            Some(Element::Nonterminal(n)) => {
                for t in grammar.borrow_production(n).unwrap().borrow_initial_tokens() {
                    if !token_set.contains(t) { token_set.push(*t); changed=true; }
                }
            },
            None => { // At end of rule - so anything that is in the token_set for the rule's nonterminal counts too
                for t in grammar.borrow_production(&rule.nonterminal).unwrap().follow_set.iter() {
                    if !token_set.contains(t) { token_set.push(*t); changed=true; }
                }
            }
        }
        changed
    }
    //mp generate_follow_set
    pub fn generate_follow_set(&self, grammar:&Grammar<F,N,T>) -> Option<Vec<T>> {
        let mut changed = false;
        let mut token_set = Vec::with_capacity(self.follow_set.len());
        for t in self.follow_set.iter() { token_set.push(*t); }
        for p in grammar.productions.iter() {
            for r in p.rules.iter() {
                for (i,e) in r.rule.iter().enumerate() {
                    if e.is_nonterminal() && (*e.borrow_nonterminal() == self.nonterminal) {
                        changed = changed || self.find_next_tokens_of_rule_position( grammar, r, i+1, &mut token_set);
                    }
                }
            }
        }
        println!("Generate_Follow_Set for {} yielded {:?}", self, token_set);
        if changed { Some(token_set)} else {None}
    }
}

//ip Display for GrammarProduction
impl <F, N:Nonterminal, T:Token> std::fmt::Display for GrammarProduction<F,N,T> {

    //mp fmt - format for display
    /// Display the rule
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[" )?;
        for r in &self.rules {
            write!(f, "{}, ", r)?;
        }
        write!(f, "]" )
    }

    //zz All done
}

//a Test for rules and productions
#[cfg(test)]
mod test_rules_productions {
    use super::*;
    impl Token for char {}
    impl Nonterminal for char {}
    #[test]
    fn test_0() {
        let mut p_a = GrammarProduction::new('A')
            .add_rule( GrammarRule::new('A',0).append_token('0').append_nonterminal('A') )
            .add_rule( GrammarRule::new('A',1).append_nonterminal('B') )
            ;
        let mut p_b = GrammarProduction::new('B')
            .add_rule( GrammarRule::new('B',2).append_token('1').append_nonterminal('B') )
            ;
        println!("p_a {}",p_a);
        println!("p_b {}",p_b);
        let mut p = vec![p_a, p_b];
        loop {
            let mut changed = false;
            let mut it = Vec::new();
            for i in 0..p.len() {
                it.push( p[i].find_initial_tokens(&p) );
            }
            let mut n=0;
            for i in it {
                if let Some(t) = i {
                    p[n].initial_tokens = t;
                    changed = true;
                }
                n += 1;
            }
            if ! changed { break; }
        }
        println!("p_a {:?}",p[0]);
        println!("p_b {:?}",p[1]);
        assert_eq!(p[0].initial_tokens, vec!['0','1']);
        assert_eq!(p[1].initial_tokens, vec!['1']);

    }
}

