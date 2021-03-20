use crate::grammar::{Token, Nonterminal, Element, Data, Grammar, GrammarRule, GrammarRulePos, GrammarProduction, ConfiguratingSet, LRAnalysis, Parser};

impl <'a, F, N:Nonterminal, T:Token, D:Data> Parser<F,N,T,D> for LRAnalysis<'a, F, N, T> {
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
        // A calculator grammar that supports BODMAS
        // Brackets highest precedence
        // Division/Multiplication next highest
        // Addition/Subtraction lowest priority
        // This assumes that all shift-reduce conflicts are resolved as shift.
        let mut p_calc = GrammarProduction::new('C')
            .add_rule( GrammarRule::new(0).append_nonterminal('E').append_token(';') )
            ;
        let mut p_e = GrammarProduction::new('E')
            .add_rule( GrammarRule::new(1).append_nonterminal('0') )
            ;
        let mut p_0 = GrammarProduction::new('0')
            .add_rule( GrammarRule::new(2).append_nonterminal('1') )
            .add_rule( GrammarRule::new(3).append_nonterminal('0').append_token('+').append_nonterminal('1') )
            .add_rule( GrammarRule::new(4).append_nonterminal('0').append_token('-').append_nonterminal('1') )
            ;
        let mut p_1 = GrammarProduction::new('1')
            .add_rule( GrammarRule::new(5).append_nonterminal('2') )
            .add_rule( GrammarRule::new(6).append_nonterminal('1').append_token('*').append_nonterminal('2') )
            .add_rule( GrammarRule::new(7).append_nonterminal('1').append_token('/').append_nonterminal('2') )
            ;
        let mut p_2 = GrammarProduction::new('2')
            .add_rule( GrammarRule::new(8).append_token('(').append_nonterminal('E').append_token(')'))
            .add_rule( GrammarRule::new(7).append_token('X') )
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
        // g.create_initial_tokens();
        // g.create_follow_sets();
        // println!("{}",g);
        let mut lr_analysis = LRAnalysis::new(&g, &g.borrow_production(&'C').unwrap().rules[0]);
        println!("{}",lr_analysis);
        lr_analysis.build_configurator_sets();
        println!("{}",lr_analysis);
        lr_analysis.parse(
            &mut vec!['X','+','X',';'].into_iter().map(|x| (Element::Token(x),0.0_f32))
        ).unwrap();
        assert!(false);
    }


