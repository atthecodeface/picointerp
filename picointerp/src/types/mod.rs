pub trait PicoBaseType : Sized {
}

pub enum PicoType<B:PicoBaseType> {
    BaseType(B),
    Tuple(Vec<usize>), // Vec so it is ordered
    Record(Vec<(String, usize)>), // Vec so it is ordered
    TaggedUnion(Vec<(String, usize)>), // Vec so it is ordered
    Function(usize, usize),
    // Array(usize),
}

impl <B:PicoBaseType> PicoType<B> {
    pub fn new_base(base:B) -> Self {
        Self::BaseType(base)
    }
    pub fn new_tuple(fields:Vec<usize>) -> Self {
        Self::Tuple(fields)
    }
    pub fn new_record(field_names:Vec<&str>, field_types:Vec<usize>) -> Self {
        assert!(field_names.len() == field_types.len());
        let mut fields = Vec::new();
        for (n,v) in field_names.iter().zip(field_types.iter()) {
            fields.push( (n.to_string(), *v) );
        }
        Self::Record(fields)
    }
    pub fn new_tagged_union(tag_names:Vec<&str>, types:Vec<usize>) -> Self {
        assert!(tag_names.len() == types.len());
        let mut options = Vec::new();
        for (n,v) in tag_names.iter().zip(types.iter()) {
            options.push( (n.to_string(), *v) );
        }
        Self::TaggedUnion(options)
    }
    pub fn new_function(arg:usize, value:usize) -> Self {
        Self::Function(arg,value)
    }
    pub fn type_of_record_field(&self, name:&str) -> Option<usize> {
        match self {
            Self::Record(fields) => {
                for (n,t) in fields.iter() {
                    if n == name { return Some(*t); }
                }
                None
            },
            _ => None,
        }
    }
    pub fn type_of_enum(&self, name:&str) -> Option<usize> {
        match self {
            Self::TaggedUnion(fields) => {
                for (n,t) in fields.iter() {
                    if n == name { return Some(*t); }
                }
                None
            },
            _ => None,
        }
    }
    //pub fn iter_tags(&self) -> impl Iterator < Item = (&str, usize) > {
    //}
}

pub struct PicoTypeSet<B:PicoBaseType> {
    // Keep a vector as it needs to be ordered!
    types: Vec<(String, PicoType<B>)>,
    //
    scope_stack : Vec<String>,
}

impl <B:PicoBaseType> PicoTypeSet<B> {
    // type TypeReference : usize ;
    pub fn new() -> Self {
        let types       = Vec::new();
        let scope_stack = Vec::new();
        Self { types, scope_stack }
    }
    pub fn push_scope(&mut self, name:&str) {
        self.scope_stack.push(name.to_string());
    }
    pub fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }
    pub fn scope_name(&self) -> String {
        let mut r = String::new();
        for s in &self.scope_stack {
            if r.len() > 0 {
                r.push_str("::");
            }
            r.push_str(s);
        }
        r
    }
    pub fn add_type(&mut self, name:&str, pico_type:PicoType<B>) -> usize {
        let n = self.types.len();
        self.types.push( (name.to_string(), pico_type) );
        n
    }
    pub fn find_type(&self, name:&str) -> Option<usize> {
        for (i,(n,_)) in self.types.iter().enumerate() {
            if n == name {
                return Some(i);
            }
        }
        None
    }
}

//a Test
#[cfg(test)]
mod test_types {
    use super::*;
enum BaseType {
    Unit,
    Int,
    Float,
}

impl PicoBaseType for BaseType {
}

type Type    = PicoType<BaseType>;
type TypeSet = PicoTypeSet<BaseType>;

fn create_types () -> TypeSet {
    let mut type_set   = TypeSet::new();
    let base_int     = type_set.add_type( "int",   Type::new_base(BaseType::Int) );
    let base_float   = type_set.add_type( "float", Type::new_base(BaseType::Float) );
    type_set.push_scope("diagram");
    type_set.push_scope("geometry");
    let point        = type_set.add_type( "point", Type::new_tuple(vec![base_float, base_float]) );
    let bbox         = type_set.add_type( "bbox",  Type::new_tuple(vec![point, point]) );
    type_set.pop_scope();
    type_set.push_scope("path");
    let path_element = type_set.add_type( "path_element", Type::new_record( vec!["flags", "width"], vec![base_int, base_float] ) );
    type_set.pop_scope();
    type_set.pop_scope();
    type_set
}
    fn test() {
        let ts = create_types();
        assert_eq!(ts.find_type("not a type"),   None);
        assert_eq!(ts.find_type("int"),   Some(0));
        assert_eq!(ts.find_type("float"), Some(1));
    }
}

/*
pub enum TypedLambdaEnum<TV> {
    Const(TV),
    Env(EnvRef),
    GetField(
    
}
    pub struct TypedLambda {
  */      
