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
use super::{Token, Nonterminal, Element, Grammar, GrammarRule, GrammarRulePos, ConfiguratingSet};

//a Constants
const DEBUG_LR_ANALYSIS : bool = 1 == 0;

//a State
///  A state in the LR parser has a configurating set and targets
/// that it can got to, and actions that it may perform.
pub struct State<'a, F, N:Nonterminal, T:Token> {
    pub(crate) cs : ConfiguratingSet<'a, usize, F, N, T>,
}

impl <'a, F, N:Nonterminal, T:Token> State<'a, F, N, T> {
    //fp new
    pub fn new() -> Self {
        Self { cs : ConfiguratingSet::new() }
    }

    //mp add_state_rule_position_closure
    /// Build the state as a closure on 'equivalent' rule positions in the grammar
    ///
    /// If state is not none, then this is going from state using
    /// (rule, position) to a new state with (rule, position+1)
    /// through the element at (rule, position). If the state already
    /// has a target for that element, then that state is the target
    /// state, and it needs to have (rule, position+1) added to it,
    /// with closure.
    ///
    /// For safe memory access this function takes a vector of
    /// GrammarRulePos that need to be added to this state for the
    /// closure; it handles one of the elements, and pushes any more
    /// that need that this leads to on to the vector.
    ///
    /// When the vector is empty, a complete closure must have been found
    pub fn add_state_rule_position_closure(&mut self, grammar:&'a Grammar<F,N,T>, mut rule_positions:Vec<GrammarRulePos<'a, F,N,T>>) {
        let rule_position = rule_positions.pop();
        if rule_position.is_none() {
            if DEBUG_LR_ANALYSIS { println!(" Completed closure"); }
            return;
        }
        let rule_position = rule_position.unwrap();
        if DEBUG_LR_ANALYSIS { println!(" Checking for state rule/position {}",rule_position); }
        if !self.cs.contains_rule_position(&rule_position) {
            if DEBUG_LR_ANALYSIS { println!(" Adding..."); }
            match rule_position.borrow_element() {
                Some(Element::Nonterminal(n)) => {
                    for r in grammar.borrow_production(n).unwrap().rules.iter() {
                        if DEBUG_LR_ANALYSIS { println!("    Add to search {} 0",r); }
                        rule_positions.push(GrammarRulePos::new(r,0));
                    }
                }
                _ => {
                },
            }
            self.cs.add_rule_position(rule_position);
        }
        self.add_state_rule_position_closure(grammar, rule_positions)
    }

    //zz All done
}

//ip Display for State
impl <'a, F, N:Nonterminal, T:Token> std::fmt::Display for State<'a,F,N,T> {

    //mp fmt - format for display
    /// Display the rule
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.cs.fmt(f)
    }
    //zz All done
}

//tp LRAnalysis
pub struct LRAnalysis<'a, F, N:Nonterminal, T:Token> {
    pub(crate) grammar : &'a Grammar<F,N,T>,
    pub(crate) goal    : &'a GrammarRule<F,N,T>,
    pub(crate) states  : Vec<State<'a, F, N, T>>,
}

//ip LRAnalysis
impl <'a, F, N:Nonterminal, T:Token> LRAnalysis<'a, F, N, T> {
    pub fn new(grammar:&'a Grammar<F,N,T>, goal:&'a GrammarRule<F,N,T>) -> Self {
        Self { grammar, goal, states:Vec::new() }
    }

    //mp find_or_add_state
    pub fn find_or_add_state(&mut self, rule_position:GrammarRulePos<'a, F, N, T>) -> usize {
        for (i,s) in self.states.iter().enumerate() {
            if s.cs.contains_rule_position(&rule_position) {
                return i;
            }
        }
        let mut s = State::new();
        s.add_state_rule_position_closure(self.grammar, vec![rule_position]);
        let n = self.states.len();
        self.states.push(s);
        n
    }

    //mp build_configurator_sets
    pub fn build_configurator_sets(&mut self) {
        self.find_or_add_state( GrammarRulePos::new(self.goal,0) );
        let mut i = 0;
        loop {
            if i >= self.states.len() { break; }
            if DEBUG_LR_ANALYSIS { println!("Looking at rules in state {} {}",i,self.states[i]); }
            let mut j = 0;
            while j < self.states[i].cs.num_rule_positions() {
                match self.states[i].cs.rule_position_next_element(j) {
                    Some(e) => {
                        // if verbose:print "State",i,"item",j,ne,rp
                        // Does state s have a target for ne? If so, add the rule/position to that - if not, add a new state with this rule/position
                        let progress_rule = self.states[i].cs.rule_position_progress_rule(j);
                        if DEBUG_LR_ANALYSIS { println!("State {} item {} element {} progress_rule {}",i,j,e, progress_rule); }
                        let ns = match self.states[i].cs.find_target(&e) {Some(ns) => Some(*ns), None=>None};
                        match ns{
                            Some(ns) => {
                                self.states[ns].add_state_rule_position_closure(self.grammar, vec![progress_rule]);
                            }
                            None => {
                                let ns = self.find_or_add_state(progress_rule);
                                self.states[i].cs.add_target(e, ns);
                            },
                        }
                    },
                    None => { // reduce rule - no other states to add
                    },
                }
                j += 1;
            }
            i += 1;
        }
    }
}

//ip Display for LRAnalysis
impl <'a, F, N:Nonterminal, T:Token> std::fmt::Display for LRAnalysis<'a,F,N,T> {

    //mp fmt - format for display
    /// Display the rule
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Grammar:\n")?;
        write!(f, "{}",self.grammar)?;
        write!(f, "Goal:\n")?;
        write!(f, "{}\n",self.goal)?;
        write!(f, "States:\n")?;
        for (i,s) in self.states.iter().enumerate() {
            write!(f, "{}:\n{}", i, s)?;
        }
        Ok(())
    }
    //zz All done
}

