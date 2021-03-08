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

@file    mode.rs
@brief   types
 */

//a Imports
use crate::ir::{PicoIRInstruction, PicoIRProgram, PicoIRIdentType};
use crate::base::{Opcode, ArithOp, LogicOp, CmpOp, BranchOp, AccessOp};

//a  PicoBaseType, PicoType
//tp PicoBaseType
/// The base trait for a PicoType
///
/// Any PicoType instance must support Unit, Bool and Int; this trait
/// permits generation of types of this sort.
pub trait PicoBaseType : Sized {
    /// Return a type of Unit
    fn of_unit() -> Self;
    /// Return a type of Int
    fn of_isize() -> Self;
    /// Return a type of Bool
    fn of_bool()  -> Self;
}

//tp PicoTypeRef
/// A reference to a PicoType
///
/// In a typeset that is a vector of PicoType's this may simply be the
/// index into the vector; for a hierarchy of modules, perhaps it
/// could be a pair of indices - one for a module, one for the type
/// within the typeset for that module
///
/// The type reference cannot have a borrow lifetime, as the types may
/// be mutually recursive. For this to be supported it is possible to
/// use Rc<RefCell<>> items.
pub trait PicoTypeRef : Sized + Copy {
}

//tp PicoType
/// This represents a base type or compound type supported by the type system.
pub enum PicoType<B:PicoBaseType, R:PicoTypeRef> {
    /// An instance of a BaseType - at minimum unit, bool, int;
    /// possibly with other base types for the system that it is being
    /// used for
    BaseType(B),
    /// A tuple of types
    Tuple(Vec<R>), // Vec so it is ordered
    Record(Vec<(String, R)>), // Vec so it is ordered
    TaggedUnion(Vec<(String, R)>), // Vec so it is ordered
    Function(R, R),
    // Array(usize),
}

//ip PicoType
impl <B:PicoBaseType, R:PicoTypeRef> PicoType<B, R> {
    //fp new_base
    pub fn new_base(base:B) -> Self {
        Self::BaseType(base)
    }
    //fp new_tuple
    pub fn new_tuple(fields:Vec<R>) -> Self {
        Self::Tuple(fields)
    }
    //fp new_record
    pub fn new_record(field_names:Vec<&str>, field_types:Vec<R>) -> Self {
        assert!(field_names.len() == field_types.len());
        let mut fields = Vec::new();
        for (n,v) in field_names.iter().zip(field_types.iter()) {
            fields.push( (n.to_string(), *v) );
        }
        Self::Record(fields)
    }
    //fp new_tagged_union
    pub fn new_tagged_union(tag_names:Vec<&str>, types:Vec<R>) -> Self {
        assert!(tag_names.len() == types.len());
        let mut options = Vec::new();
        for (n,v) in tag_names.iter().zip(types.iter()) {
            options.push( (n.to_string(), *v) );
        }
        Self::TaggedUnion(options)
    }
    //fp new_function
    pub fn new_function(arg:R, value:R) -> Self {
        Self::Function(arg,value)
    }
    //mp type_of_record_field
    pub fn type_of_record_field(&self, name:&str) -> Option<R> {
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
    //mp type_of_enum
    pub fn type_of_enum(&self, name:&str) -> Option<R> {
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
    //pub fn iter_tags(&self) -> impl Iterator < Item = (&str, R) > {
    //}
}

//tp PicoTypeSet
impl PicoTypeRef for usize {
}
pub struct PicoTypeSet<B:PicoBaseType> {
    // Keep a vector as it needs to be ordered!
    types: Vec<(String, PicoType<B, usize>)>,
    //
    scope_stack : Vec<String>,
}

//ip PicoTypeSet
impl <B:PicoBaseType> PicoTypeSet<B> {
    // type TypeReference : usize ;
    //fp new
    pub fn new() -> Self {
        let types       = Vec::new();
        let scope_stack = Vec::new();
        Self { types, scope_stack }
    }
    //fp push_scope
    pub fn push_scope(&mut self, name:&str) {
        self.scope_stack.push(name.to_string());
    }
    //fp pop_scope
    pub fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }
    //fp scope_name
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
    //fp add_type
    pub fn add_type(&mut self, name:&str, pico_type:PicoType<B, usize>) -> usize {
        let n = self.types.len();
        self.types.push( (name.to_string(), pico_type) );
        n
    }
    //fp find_type
    pub fn find_type(&self, name:&str) -> Option<usize> {
        for (i,(n,_)) in self.types.iter().enumerate() {
            if n == name {
                return Some(i);
            }
        }
        None
    }
    //zz All done
}

//a Test
#[cfg(test)]
mod test_types {
    use super::*;
    enum BaseType {
        Unit,
        Bool,
        Int,
        Float,
    }

    impl PicoBaseType for BaseType {
        fn of_unit()  -> Self { BaseType::Unit }
        fn of_bool()  -> Self { BaseType::Bool }
        fn of_isize() -> Self { BaseType::Int }
    }

    type Type    = PicoType<BaseType, usize>;
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

