mod types;
mod rule;
mod production;
mod grammar;

pub use self::types::{Token, Nonterminal, Element};
pub use self::rule::{GrammarRule};
pub use self::production::{GrammarProductionTokenIter, GrammarProduction};
pub use self::grammar::Grammar;

//a Ignore me

/*
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
/// Note that 'S -> . E' is alson in the configurating set.
///
/// The configurating set also has a set of (t,e) -> targets,
/// where t is token/nonterminal, and e is a token or nonterminal.
/// All rule/positions in the configurating set that share a next
/// element of (t,e) have the same target (another configurating
/// set)
///
/// What this means is that 'S -> . E' and 'E -> . E + T' have the
/// same target configurating set.
///
struct ConfiguratingSet<'a> {
    rule_positions : Vec<GrammarRulePos<'a>>,
    targets        : Vec<(Type,Element)>,
    conflicts      : usize,
}

impl <'a>ConfiguratingSet<'a> {
    //fp new
    pub fn new() -> Self {
        let rule_positions = Vec::new();
        let targets   = ;
        let conflicts = ;
        Self { rule_positions, targets, conflicts }
    }
    //mp add_rule_position
    /// 'rule' is a grammar production rule, and 'position' is 0
    /// for prior to the first element, 1 for between the first
    /// and second element, and so on.
    pub fn add_rule_position(&'a mut self, rule:&'a GrammarRulePos<'a>) -> None {
        self.rule_positions.push(rule)
    }

    //mp contains_rule_position
    pub fn contains_rule_position(&self, rule_position:&GrammarRulePos) -> bool {
        self.rule_positions.contains(rule_position)
    }

    //mp rule_position_next_element
    pub fn <'a>rule_position_next_element(&self, n:usize) {
        let (r,p) = self.rule_positions[n];
        r.element(p)
    }

    //mp find_target
    /// Find a (t,e) target if the set has it, otherwise return None
    pub fn find_target(&self, type_element:(Type,Element)) -> Option<&(Type,Element)> {
        for t in &self.targets {
            if *t == *type_element {
                return Some(t);
            }
        }
        None
    }
    //mp add_target
    pub fn add_target(&mut self, type_element:(Type,Element), s:) {
        self.targets[type_element] = s;
    }
    //mp rule_position_progress_rule
    pub fn rule_position_progress_rule(&self ) {
        let (r,p) = self.rule_positions[n];
        let p = p + 1;
        if p > r.len() { panic!("Attempt to move beyond end of rule %s/%d"%(str(r),p)); }
        return (r,p);
    }
    //mp num_rule_positions
    pub fn num_rule_positions(&self) -> usize {
        return self.rule_positions.len();
    }
    //mp get_reduce_rule_positions
    pub fn get_reduce_rule_positions(&self) -> Vec<>{
        let reduce_rps = Vec::new();
        for rp in &self.rule_positions {
            if rp[0].element(rp[1]) is None {
                reduce_rps.append(rp)
            }
        }
        return reduce_rps;
    }
    //mp analyze
    /// Generate conflicts sets
    pub fn analyze(&mut self) {
        let reduce_rps = self.get_reduce_rule_positions();
        if reduce_rps.len() > 1 {
            self.conflicts["reduce-reduce"] = reduce_rps;
        }
        if reduce_rps.len() > 0 && self.rule_positions.len() > 1 {
            self.conflicts["shift-reduce"] = reduce_rps;
        }
    }
    //mp get_expected_tokens
    pub fn get_expected_tokens(&self) -> Vec<> {
        let tokens = Vec::new();
        for (r,p) in &self.rule_positions {
            if let Some(ne) = r.element(p) {
                if ne.0 == "token" {
                    if ne[1] not in tokens {
                        tokens.append(ne[1])
                    }
                }
            }
        }
        tokens
    }

    //zz All done
}
*/
