use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;
use std::collections::{HashMap, HashSet};
pub trait Token : Sized + Display + Eq + Hash + Copy + Debug {
}
pub trait Nonterminal : Sized + Display + Eq + Hash + Copy + Debug {
}
#[derive(Debug)]
pub enum Element<N:Nonterminal, T:Token> {
    Token(T),
    Nonterminal(N),
}
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
    nonterminal : N,
    /// The rule itself
    rule        : Vec<Element<N,T>>,
    /// Function to invoke on reduction
    rule_fn     : F,
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
    nonterminal : N,
    rules       : Vec<GrammarRule<F,N,T>>,
    initial_tokens : Vec<T>,
    /// The follow_set for a nonterminal is the set of tokens that
    /// *may* come after this production legally in the grammar. This
    /// can be used to handle reduce-reduce conflicts using lookahead
    /// - if the lookahead token is *not* in the follow_set, then this
    /// reduction is *not* permitted - but a different reduction may
    /// be
    follow_set : Vec<T>,
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
    productions : Vec<GrammarProduction<F,N,T>>,
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
        assert!(g.borrow_production(&'E').unwrap().follow_set == vec!['@'], "E can be followed by '@'");
        assert!(g.borrow_production(&'A').unwrap().follow_set.len()==0, "There should be an empty follow set for A");
        assert!(g.borrow_production(&'0').unwrap().follow_set == vec!['a'], "0 can be followed by 'a'");
        assert!(g.borrow_production(&'1').unwrap().follow_set == vec!['b'], "1 can be followed by 'b'");
    }
}


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
