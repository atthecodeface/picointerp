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

@file    grammar.rs
@brief   Part of grammar library
 */

//a Imports
use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use super::{Token, Nonterminal, Element, GrammarProduction, GrammarRule};

//a Grammar
//tp Grammar
/// tokens is a 'production terminal' -> 'output value' mapping for
/// terminals that are permitted to appear in a production; they are
/// elements that the lexical analyzer may produce.
///
/// productions are 'nonterminal' -> 'sequence of (rule, reduction
/// function)' mappings
///
/// A grammar cannot be valid if the rules include anything that are
/// not production terminals or production nonterminals.
#[derive(Debug)]
pub struct Grammar<F, N:Nonterminal, T:Token> {
    /// Name of the grammar for display
    name   : String,
    /// A set of the permitted tokens
    token_set      : HashSet<T>,
    /// All of the productions in the grammar
    pub(crate) productions : Vec<GrammarProduction<F,N,T>>,
    /// A map from nonterminal to index into productions for each nonterminal
    productions_of_nonterminal : HashMap<N,usize>,
}

//ip Grammar
impl <F, N:Nonterminal, T:Token> Grammar<F, N, T> {
    //fp new
    pub fn new(name:&str, tokens:Vec<T>) -> Self {
        let name = name.to_string();
        let mut token_set = HashSet::new();
        for t in tokens {
            token_set.insert(t);
        }
        let productions = Vec::new();
        let productions_of_nonterminal = HashMap::new();
        Self { name, token_set, productions, productions_of_nonterminal }
    }
    //cp add_production
    pub fn add_production(mut self, production:GrammarProduction<F,N,T>) -> Self {
        let n = production.nonterminal;
        assert!(!self.productions_of_nonterminal.contains_key(&n), "Duplicate production set for nonterminal {}", n);
        let l = self.productions.len();
        let v = self.productions_of_nonterminal.insert(n,l);
        self.productions.push(production);
        self
    }
    //mp validate
    pub fn validate(&self) -> Result<(),Vec<String>> {
        let mut errors = Vec::new();
        for p in &self.productions {
            for e in p.iter_elements() {
                match e {
                    Element::Token(t) => {
                        if ! self.token_set.contains(t) {
                            errors.push(format!("Token {} unknown in grammar",t));
                        }
                    },
                    Element::Nonterminal(n) => {
                        if ! self.productions_of_nonterminal.contains_key(n) {
                            errors.push(format!("Nonterminal {} unknown in production {}",n,p));
                        }
                    },
                }
            }
        }
        if errors.len() > 0 { Err(errors) } else { Ok(()) }
    }
    //mp borrow_production
    pub fn borrow_production<'a>(&'a self, n:&N) -> Option<&'a GrammarProduction<F,N,T>> {
        match self.productions_of_nonterminal.get(n) {
            None => None,
            Some(n) => Some(&self.productions[*n]),
        }
    }
    //mp create_initial_tokens
    pub fn create_initial_tokens(&mut self) {
        let num_productions = self.productions.len();
        loop {
            let mut changed = false;
            let mut it = Vec::with_capacity(num_productions);
            for i in 0 .. num_productions {
                it.push( self.productions[i].find_initial_tokens( &self.productions ) );
            }
            let mut n=0;
            for i in it {
                if let Some(t) = i {
                    self.productions[n].initial_tokens = t;
                    changed = true;
                }
                n += 1;
            }
            if ! changed { break; }
        }
    }
    //mp create_follow_sets
    pub fn create_follow_sets(&mut self) {
        let num_productions = self.productions.len();
        loop {
            let mut changed = false;
            let mut it = Vec::with_capacity(num_productions);
            for i in 0 .. num_productions {
                it.push( self.productions[i].generate_follow_set(self) );
            }
            let mut n=0;
            for i in it {
                if let Some(t) = i {
                    self.productions[n].follow_set = t;
                    changed = true;
                }
                n += 1;
            }
            if ! changed { break; }
        }
    }
    //zz All done
}

//ip Display for Grammar
impl <F, N:Nonterminal, T:Token> std::fmt::Display for Grammar<F,N,T> {

    //mp fmt - format for display
    /// Display the grammar
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Grammar {}\n", self.name)?;
        write!(f, "    tokens:")?;
        for t in self.token_set.iter() {
            write!(f, " {}", t)?;
        }
        write!(f, "\n");
        write!(f, "    nonterminals:")?;
        for t in self.productions_of_nonterminal.keys() {
            write!(f, " {}", t)?;
        }
        write!(f, "\n");
        write!(f, "    grammar:\n");
        for p in self.productions.iter() {
            for r in p.rules.iter() {
                write!(f, "        {}\n", r)?;
            }
        }
        Ok(())
    }

    //zz All done
}

//a Test for grammar
#[cfg(test)]
mod test_grammar {
    use super::*;
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
        let mut g = Grammar::new("AB", vec!['0', '1'])
            .add_production(p_a)
            .add_production(p_b)
            ;
        g.validate().unwrap();
        println!("{}",g);
        g.create_initial_tokens();
        g.create_follow_sets();
        println!("{}",g);
        println!("{:?}",g);
        assert!(g.borrow_production(&'A').unwrap().follow_set.len()==0, "There should be an empty follow set for A");
        assert!(g.borrow_production(&'B').unwrap().follow_set.len()==0, "There should be an empty follow set for B");
    }
    #[test]
    fn test_1() {
        // A very simple grammar with a reduce-reduce conflict

        // An LR(0) parser cannot determine the reduction to use in the
        // reduce-reduce conflict

        // Hence it cannot parse both c a @ and c b @ - it must fail on
        // one of these.

        // An SLR parser should be able to cope, using a follow-set for '1'
        // of 'b', and a follow-set for '0' of 'a'.  At the point of the
        // reduce-reduce conflict the SLR parser can look at the next token
        // and check perform one of the reductions, assuming the token is in
        // one of the reduction's follow sets.
        //
        // goal = "all"
        // test_string ="C A EOF"
        // test_result = ""
        let mut p_e = GrammarProduction::new('E')
            .add_rule( GrammarRule::new('E',0).append_nonterminal('1').append_token('b') )
            .add_rule( GrammarRule::new('E',1).append_nonterminal('0').append_token('a') )
            ;
        let mut p_1 = GrammarProduction::new('0')
            .add_rule( GrammarRule::new('0',2).append_token('c') )
            ;
        let mut p_2 = GrammarProduction::new('1')
            .add_rule( GrammarRule::new('1',3).append_token('c') )
            ;
        let mut p_all = GrammarProduction::new('A')
            .add_rule( GrammarRule::new('A',4).append_nonterminal('E').append_token('@') )
            ;
        let mut g = Grammar::new("Reduce-reduce conflict grammar", vec!['@', 'a', 'b', 'c'])
            .add_production(p_all)
            .add_production(p_e)
            .add_production(p_1)
            .add_production(p_2)
            ;
        g.validate().unwrap();
        println!("{}",g);
        g.create_initial_tokens();
        g.create_follow_sets();
        println!("{}",g);
        println!("{:?}",g);
        assert_eq!(g.borrow_production(&'E').unwrap().follow_set, vec!['@'], "E can be followed by '@'");
        assert_eq!(g.borrow_production(&'A').unwrap().follow_set.len(), 0, "There should be an empty follow set for A");
        assert_eq!(g.borrow_production(&'0').unwrap().follow_set, vec!['a'], "0 can be followed by 'a'");
        assert_eq!(g.borrow_production(&'1').unwrap().follow_set, vec!['b'], "1 can be followed by 'b'");
    }
    #[test]
    fn test_calc() {
        // A calculator grammar that supports BODMAS
        // Brackets highest precedence
        // Division/Multiplication next highest
        // Addition/Subtraction lowest priority
        // This assumes that all shift-reduce conflicts are resolved as shift.
        let mut p_calc = GrammarProduction::new('C')
            .add_rule( GrammarRule::new('C',0).append_nonterminal('E').append_token(';') )
            ;
        let mut p_e = GrammarProduction::new('E')
            .add_rule( GrammarRule::new('E',1).append_nonterminal('0') )
            ;
        let mut p_0 = GrammarProduction::new('0')
            .add_rule( GrammarRule::new('0',2).append_nonterminal('1') )
            .add_rule( GrammarRule::new('0',3).append_nonterminal('0').append_token('+').append_nonterminal('1') )
            .add_rule( GrammarRule::new('0',4).append_nonterminal('0').append_token('-').append_nonterminal('1') )
            ;
        let mut p_1 = GrammarProduction::new('1')
            .add_rule( GrammarRule::new('1',5).append_nonterminal('2') )
            .add_rule( GrammarRule::new('1',6).append_nonterminal('1').append_token('*').append_nonterminal('2') )
            .add_rule( GrammarRule::new('1',7).append_nonterminal('1').append_token('/').append_nonterminal('2') )
            ;
        let mut p_2 = GrammarProduction::new('2')
            .add_rule( GrammarRule::new('2',8).append_token('(').append_nonterminal('E').append_token(')'))
            .add_rule( GrammarRule::new('1',7).append_token('X') )
            ;
        let mut g = Grammar::new("calculator grammar", vec![';', 'X', '+', '-', '*', '/', '(', ')'])
            .add_production(p_calc)
            .add_production(p_e)
            .add_production(p_0)
            .add_production(p_1)
            .add_production(p_2)
            ;
        g.validate().unwrap();
        println!("{}",g);
        g.create_initial_tokens();
        g.create_follow_sets();
        println!("{}",g);
        println!("{:?}",g);
        assert_eq!(g.borrow_production(&'C').unwrap().follow_set.len(), 0 );
        assert_eq!(g.borrow_production(&'E').unwrap().follow_set, vec![';', ')'] );
        assert_eq!(g.borrow_production(&'0').unwrap().follow_set, vec!['+', ';', ')', '-'] );
        assert_eq!(g.borrow_production(&'1').unwrap().follow_set, vec!['*', '+', ';', ')', '-', '/'] );
        assert_eq!(g.borrow_production(&'2').unwrap().follow_set, vec!['*', '+', ';', ')', '-', '/'] );
    }
}


