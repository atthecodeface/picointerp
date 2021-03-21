use crate::grammar::{Token, Nonterminal, Element, Data, Grammar, GrammarRule, GrammarRulePos, GrammarProduction, ConfiguratingSet, LRAnalysis, Parser, Parsable};
use super::grammars::calculator_expanded;

impl <'a, F, N:Nonterminal, T:Token, D:Data> Parsable<F,N,T,D> for LRAnalysis<'a, F, N, T> {
    fn initial_state(&self) -> usize { 0 }
    fn find_shift_state(&self, state:usize, e:&Element<N,T>) -> Option<&usize> {
        self.states[state].cs.find_target(e)
    }
    fn find_reduce_rule(&self, state:usize, e:Option<&T>) -> Option<&GrammarRule<F,N,T>> {
        for rp in self.states[state].cs.rule_positions.iter() {
            if rp.is_end() { return Some(rp.rule); }
        }
        None
    }
    fn is_goal_rule(&self, rule:&GrammarRule<F,N,T>) -> bool {
        rule == self.goal
    }
}
impl Data for f32 {}
//a Test for lr_analysis
#[test]
fn test_calc() {
    let g = calculator_expanded::new();

    let mut lr_analysis = LRAnalysis::new(&g, &g.borrow_production(&calculator_expanded::N::Calc).unwrap().rules[0]);
    println!("{}",lr_analysis);
    lr_analysis.build_configurator_sets();
    println!("{}",lr_analysis);
    let mut parser = Parser::new(&lr_analysis);

    let mut blah = vec!['X','-','X',';'].into_iter().enumerate().map(|(i,x)| (Element::Token(x),0.5+(i as f32)*1.1));
    assert!((-2.2 - calculator_expanded::calculate(&mut parser, &mut blah)).abs() < 1E-6);
}


