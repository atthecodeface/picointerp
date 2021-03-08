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
use crate::types::{PicoBaseType, PicoType, PicoTypeRef};

//a  PicoTypeSet
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

