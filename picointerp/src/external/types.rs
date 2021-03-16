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

@file    external/types.rs
@brief   Part of geometry library
 */

//a Imports
use crate::{PicoValue, PicoHeap, PicoStack};
use crate::{ExtFn, ExtObjectPool};

//tp ExtType
pub struct ExtType<Ob, Pl:ExtObjectPool<Ob>, V> {
    fns : Vec<(String, ExtFn<Ob, Pl, V>)>,
}
impl <Ob, Pl:ExtObjectPool<Ob>, V> std::fmt::Debug for ExtType<Ob, Pl, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"Type[")?;
        for (n,_) in &self.fns {
            write!(f,"<Fn {}> ",n)?;
        }
        write!(f,"]")
    }
}
//pi ExtType
impl <Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtType<Ob, Pl, V> {
    //mp get_field_index
    pub fn get_field_index(&self, s:&str) -> Option<usize> {
        for (i,(n,_)) in self.fns.iter().enumerate() {
            if n == s { return Some(i) }
        }
        None
    }

    //mp invoke
    pub fn invoke<H:PicoHeap<V>, S:PicoStack<V>>(&self, fn_number:usize, pool:&mut Pl, interp_heap:&mut H, interp_stack:&mut S) -> Result<V,String> {
        if fn_number >= self.fns.len() {
            Err(format!("Function number {} out of range", fn_number))
        } else {
            self.fns[fn_number].1.invoke(pool, interp_heap, interp_stack)
        }
    }

    //fp of_fns
    pub fn of_fns( fns:Vec<(&str,ExtFn<Ob, Pl, V>)> ) -> Self {
        let mut v = Vec::new();
        for (n,f) in fns {
            v.push( (n.to_string(),f) );
        }
        Self { fns:v }
    }
    //zz All done
}

