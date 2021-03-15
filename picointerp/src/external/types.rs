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
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use crate::{PicoInterp, PicoProgram, PicoTrace, PicoValue, PicoHeap, PicoStack, PicoTag, PicoExecCompletion};
use crate::{PicoTraceStdout};
use crate::{PicoProgramU32};
use crate::{PicoIRAssembler, PicoIREncoding, PicoIRProgram, PicoIRIdentType, PicoIRResolution};
use super::function::*;

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
    //mp invoke_closure
    pub fn invoke_closure<H:PicoHeap<V>, S:PicoStack<V>> (&self, index:usize, handle:V, interp_heap:&mut H, interp_stack:&mut S,) -> V {
        let x = interp_stack.pop();
        println!("Evaluate {} * {}",x.as_isize(), handle.as_isize());
        let r = V::int(x.as_isize() * handle.as_isize());
        r
    }
    //mp interp_create_closures_for_instance
    pub fn interp_create_closures_for_instance<H:PicoHeap<V>>(&self, interp_heap:&mut H, handle:V) -> Vec<V> {
        let mut v = Vec::new();
        for i in 0..self.fns.len() {
            v.push( interp_heap.create_closure(0x80000000+i, vec![handle]) );
        }
        v
    }
    //mp interp_create_type_record_for_instance
    pub fn interp_create_type_record_for_instance<H:PicoHeap<V>>(&self, interp_heap:&mut H, handle:V) -> V {
        let record = interp_heap.alloc(PicoTag::Record as usize, self.fns.len());
        let v = self.interp_create_closures_for_instance(interp_heap, handle);
        let mut n = 0;
        for c in v {
            interp_heap.set_field(record, n, c);
            n += 1;
        }
        record
    }
}

