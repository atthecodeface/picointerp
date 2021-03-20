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

@file    configurating_set.rs
@brief   Part of grammar library
 */

//a Imports
use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::{HashMap, HashSet};
use super::{Token, Nonterminal, Element, Grammar, GrammarRule, GrammarRulePos};

//a ConfiguratingSet
//tp ConfiguratingSet
/// A configurating set in an LR parser is a set of positions
/// inside rules - the position is 'just before' an element of a
/// rule. The set is, in essence, a summary of the identical
/// rule positions that a parser might be in.
///
/// For example, in a grammar
/// S -> E ;
/// E -> E + T
/// E -> T
/// T -> ( E )
/// T -> id
///
/// the configurating set that includes 'E -> . E + T'
/// (. indicates the position the parser is in - what it is
/// expecting next) also includes 'E -> . T' (as E is the item
/// following the . in the initial rule/position); hence also
/// 'T -> . ( E )' must be in the configurating set as must
/// 'T -> . id', as T is the item following the '.' in the
/// (now) second entry in the configurating set.
///
/// Note that 'S -> . E' is also in the configurating set.
///
/// The configurating set also has a set of Element -> targets.
/// All rule/positions in the configurating set that share a next
/// element have the same target (another configurating
/// set)
///
/// What this means is that 'S -> . E' and 'E -> . E + T' have the
/// same target configurating set.
///
pub struct ConfiguratingSet<'a, Tgt, F, N:Nonterminal, T:Token> {
    /// A list of rules and positions that the configurating set consists of
    pub(crate) rule_positions : Vec<GrammarRulePos<'a, F, N, T>>,
    /// The targets
    targets        : HashMap<Element<N,T>, Tgt>,
    conflicts      : usize,
}

impl <'a, Tgt, F, N:Nonterminal, T:Token> ConfiguratingSet<'a, Tgt, F, N, T> {
    //fp new
    pub fn new() -> Self {
        let rule_positions = Vec::new();
        let targets   = HashMap::new();
        let conflicts = 0;
        Self { rule_positions, targets, conflicts }
    }

    //mp add_rule_position
    /// 'rule' is a grammar production rule, and 'position' is 0
    /// for prior to the first element, 1 for between the first
    /// and second element, and so on.
    pub fn add_rule_position(&mut self, rule:GrammarRulePos<'a, F, N, T>) {
        self.rule_positions.push(rule)
    }

    //mp borrow_rule_position
    pub fn borrow_rule_position(&self, n:usize) -> &GrammarRulePos<F, N, T> {
        &self.rule_positions[n]
    }

    //mp contains_rule_position
    pub fn contains_rule_position(&self, rule_position:&GrammarRulePos<F, N, T>) -> bool {
        self.rule_positions.contains(rule_position)
    }

    //mp rule_position_next_element
    /// Get the element that the rule position is pointing at - i.e. what is coming next
    pub fn rule_position_next_element(&self, n:usize) -> Option<Element<N,T>> {
        match self.rule_positions[n].borrow_element() {
            Some(e) => Some(*e),
            None => None,
        }
    }

    //mp rule_position_progress_rule
    pub fn rule_position_progress_rule(&self, n:usize) -> GrammarRulePos<'a, F, N, T> {
        self.rule_positions[n].progress_rule()
    }

    //mp num_rule_positions
    pub fn num_rule_positions(&self) -> usize {
        return self.rule_positions.len();
    }

    //mp find_target
    /// Find a (t,e) target if the set has it, otherwise return None
    pub fn find_target(&self, element:&Element<N, T>) -> Option<&Tgt> {
        self.targets.get(element)
    }

    //mp add_target
    pub fn add_target(&mut self, element:Element<N, T>, s:Tgt) {
        self.targets.insert(element, s);
    }

    //mp get_expected_tokens
    pub fn get_expected_tokens(&self) -> Vec<T> {
        let mut tokens = Vec::new();
        for rp in &self.rule_positions {
            match rp.borrow_element() {
                Some(Element::Token(t)) => {
                    if !tokens.contains(t) {tokens.push(*t);}
                },
                _ => (),
            }
        }
        tokens
    }

    //mp get_reduce_rule_positions
    pub fn get_reduce_rule_positions(&self) -> Vec<&GrammarRulePos<F,N,T>> {
        let mut reduce_rps = Vec::new();
        for rp in &self.rule_positions {
            if rp.is_end() {
                reduce_rps.push(rp)
            }
        }
        return reduce_rps;
    }

    //mp analyze
    /// Generate conflicts sets
    pub fn analyze(&mut self) {
    }
    /*
        let reduce_rps = self.get_reduce_rule_positions();
        if reduce_rps.len() > 1 {
            self.conflicts["reduce-reduce"] = reduce_rps;
        }
        if reduce_rps.len() > 0 && self.rule_positions.len() > 1 {
            self.conflicts["shift-reduce"] = reduce_rps;
        }
    }
     */

    //zz All done
}

//ip Display for ConfiguratingSet
impl <'a, Tgt:Display, F, N:Nonterminal, T:Token> std::fmt::Display for ConfiguratingSet<'a, Tgt,F,N,T> {

    //mp fmt - format for display
    /// Display the rule
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for rp in self.rule_positions.iter() {
            write!(f, "  {}\n", rp)?;
        }
        for (n,t) in self.targets.iter() {
            write!(f, "{} => {},", n, t)?;
        }
        write!(f, "\n")
    }
    // conflicts      : usize,

    //zz All done
}

