//md calculator_expanded
/// A calculator grammar that supports BODMAS
/// Brackets highest precedence
/// Division/Multiplication next highest
/// Addition/Subtraction lowest priority
/// This assumes that all shift-reduce conflicts are resolved as shift.
///
/// For the input X + X ; this will go through:
///
///  [0]        []      . [X + X ;]    s[X]
///  [0 5]      [X]     . [+ X ;]      r(9)
///  [0]        []      2 [+ X ;]      s(2)
///  [0 4]      [2]     . [+ X ;]      r(5)
///  [0]        []      1 [+ X ;]      s(1)
///  [0 3]      [1]     . [+ X ;]      r(2)
///  [0]        []      0 [+ X ;]      s(0)
///  [0 2]      []      . [+ X ;]      s(+)
///  [0 2 9]    [0 +]   . [X ;]        s(X)
///  [0 2 9 5]  [0 + X] . [;]         r(9)
///  [0 2 9]    [0 + 2] 2 [;]        s(2)
///  [0 2 9 4]  [0 + 2] . [;]        r(5)
///  [0 2 9]    [0 + 1] 1 [;]        s(1)
///  [0 2 9 14] [0 + 1] . [;]        r(3)
///  [0]        [.]     0 [;]        s(0)
///  [0 2]      [0]     . [;]        r(1)
///  [0]        []      E [;]        s(E)
///  [0 1]      [E]     . [;]        s(;)
///  [0 1 7]    [E ;]   . []         r(0)
///  [0]        []      C []
pub mod calculator_expanded {
    //im Imports
    use crate::grammar::{Token, Nonterminal, Grammar, GrammarRule, GrammarProduction, Parser, Element};

    //tp N - Nonterminals
    /// Enumeration for the nonterminals
    #[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
    pub enum N {
        Calc, Expr, OptSum, OptProd, BraNum
    }
    impl std::fmt::Display for N { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { write!(f,"{:?}", self) } }
    impl Nonterminal for N {}
    //tp F - Functions for reductions
    #[derive(Debug)]
    pub enum F {
        Add, Sub, Mul, Div, End, None
    }
    pub fn new() -> Grammar<F,N,char> {
        let mut p_calc = GrammarProduction::new(N::Calc)
            .add_rule( GrammarRule::new(F::End).append_nonterminal(N::Expr).append_token(';') )
            ;
        let mut p_e = GrammarProduction::new(N::Expr)
            .add_rule( GrammarRule::new(F::None).append_nonterminal(N::OptSum) )
            ;
        let mut p_0 = GrammarProduction::new(N::OptSum)
            .add_rule( GrammarRule::new(F::None).append_nonterminal(N::OptProd) )
            .add_rule( GrammarRule::new(F::Add).append_nonterminal(N::OptSum).append_token('+').append_nonterminal(N::OptProd) )
            .add_rule( GrammarRule::new(F::Sub).append_nonterminal(N::OptSum).append_token('-').append_nonterminal(N::OptProd) )
            ;
        let mut p_1 = GrammarProduction::new(N::OptProd)
            .add_rule( GrammarRule::new(F::None).append_nonterminal(N::BraNum) )
            .add_rule( GrammarRule::new(F::Mul).append_nonterminal(N::OptProd).append_token('*').append_nonterminal(N::BraNum) )
            .add_rule( GrammarRule::new(F::Div).append_nonterminal(N::OptProd).append_token('/').append_nonterminal(N::BraNum) )
            ;
        let mut p_2 = GrammarProduction::new(N::BraNum)
            .add_rule( GrammarRule::new(F::None).append_token('(').append_nonterminal(N::Expr).append_token(')'))
            .add_rule( GrammarRule::new(F::None).append_token('X') )
            ;
        let mut g = Grammar::new("calculator grammar", vec![';', 'X', '+', '-', '*', '/', '(', ')'])
            .add_production(p_calc)
            .add_production(p_e)
            .add_production(p_0)
            .add_production(p_1)
            .add_production(p_2)
            ;
        g.validate().unwrap();
        g
    }
    pub fn calculate(parser:&mut Parser<F,N,char,f32>, next_token:&mut impl Iterator<Item = (Element<N,char>,f32)>) -> f32 {
        let mut result = 0.0;
        loop {
            match parser.parse_to_reduction(next_token) {
                Ok((n, is_final, rule, mut data)) => {
                    println!("{} Rule {} data {:?}", is_final, rule, data);
                    if is_final { result = data.pop().unwrap(); break; }
                    if data.len()==1 {
                        parser.reduction_result(n, data[0] );
                    } else {
                        match rule.rule_fn {
                            F::Add  => parser.reduction_result(n, data[2] + data[0] ),
                            F::Sub  => parser.reduction_result(n, data[2] - data[0] ),
                            F::Mul  => parser.reduction_result(n, data[2] * data[0] ),
                            F::Div  => parser.reduction_result(n, data[2] / data[0] ),
                            _ => { panic!("Rule function {:?} should not occur", rule.rule_fn ); },
                        }
                    }
                }
                Err(e) => {
                    panic!("Error {}",e);
                }
            }
        }
        println!("Result {}",result);
        result
    }
}
