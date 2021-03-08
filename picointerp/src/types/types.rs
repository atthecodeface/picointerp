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
pub trait PicoTypeRef : Sized + Clone {
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
            fields.push( (n.to_string(), v.clone()) );
        }
        Self::Record(fields)
    }
    //fp new_tagged_union
    pub fn new_tagged_union(tag_names:Vec<&str>, types:Vec<R>) -> Self {
        assert!(tag_names.len() == types.len());
        let mut options = Vec::new();
        for (n,v) in tag_names.iter().zip(types.iter()) {
            options.push( (n.to_string(), v.clone()) );
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
                    if n == name { return Some(t.clone()); }
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
                    if n == name { return Some(t.clone()); }
                }
                None
            },
            _ => None,
        }
    }
    //pub fn iter_tags(&self) -> impl Iterator < Item = (&str, R) > {
    //}
}

