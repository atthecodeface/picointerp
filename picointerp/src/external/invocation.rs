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

@file    external/module.rs
@brief   Module
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
use super::name::ExtName;
use super::types::*;
use super::module::*;

//a InvTypeIter
//tp InvTypeIter
/// An iterator over the types used in the invocation
///
pub struct InvTypeIter<'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue>  {
    invocation : &'a ExtInvocation<'a, Ob, Pl, V>,
    hash_iter  : std::collections::hash_map::Iter<'a, String, (usize,Vec<(String,usize)>)>,
    ext_type_fields   : Option<(&'a ExtType<Ob, Pl, V>, &'a Vec<(String, usize)>)>,
    field_index : usize,
}

//pi InvTypeIter
impl <'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> InvTypeIter<'a, Ob, Pl, V>  {
    //fp new
    pub fn new(invocation:&'a ExtInvocation<'a, Ob, Pl, V>) -> Self {
        let hash_iter = invocation.env_type_fields.iter();
        Self { invocation, hash_iter, ext_type_fields:None, field_index:0 }
    }

    //zz All done
}

//ip Iterator for InvTypeIter
impl <'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> Iterator for InvTypeIter<'a, Ob, Pl, V> {
    /// Item is a pair of points that make a straight line
    type Item = (&'a ExtType<Ob, Pl, V> , usize);
    //mp next
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((t,f)) = self.ext_type_fields {
            if let Some((field,_)) = f.get(self.field_index) {
                let n = t.get_field_index(&field).unwrap();
                self.field_index += 1;
                Some((t, n))
            } else {
                self.ext_type_fields = None;
                self.next()
            }
        } else {
            match self.hash_iter.next() {
                None => None,
                Some((type_name, field_names)) => {
                    let ext_type = self.invocation.toplevel.find_type_of_string(type_name).unwrap().0;
                    self.ext_type_fields = Some((ext_type, &field_names.1));
                    self.field_index = 0;
                    self.next()
                }
            }
        }
    }

    //zz All done
}

//a ExtInvocation
//tp ExtInvocation
pub struct ExtInvocation<'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> {
    toplevel        : &'a ExtModule<Ob, Pl, V>,
    stack_env       : Vec<&'a str>,
    env_type_fields : HashMap::<String,(usize,Vec<(String,usize)>)>,
    num_types       : usize
}

//ip ExtInvocation
impl <'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtInvocation<'a, Ob, Pl, V> {
    //fp new
    /// Create a new invocation environment
    pub fn new(toplevel:&'a ExtModule<Ob, Pl, V>, stack_env:Vec<&'a str>) -> Self {
        let env_type_fields = HashMap::new();
        Self { toplevel, stack_env, env_type_fields, num_types:0 }
    }
    //mp enumerate
    /// Once the required types and fields are recorded, enumerate them
    pub fn enumerate(&mut self) {
        let mut index = 0;
        for (_, (ref mut n, fields)) in self.env_type_fields.iter_mut() {
            *n = index;
            index += 1;
            for (i, ref mut f) in fields.iter_mut().enumerate() {
                f.1 = i;
            }
        }
        self.num_types = index;
        println!("Enumerated {} types",self.num_types);
        println!("{:?}",self.env_type_fields);
    }
    //mp iter_env
    pub fn iter_env<'z>(&'z self) -> InvTypeIter<'z, Ob, Pl, V> {
        InvTypeIter::new(self)
    }
    //mp record_id
    fn record_id(&mut self, id_type:PicoIRIdentType, id:&str) -> PicoIRResolution {
        match id_type {
            PicoIRIdentType::EnvAcc => {
                let (depth, remaining) = {
                    if let Some((_,depth,v)) = self.toplevel.find_type_of_string(id) {
                        (depth, v.len())
                    } else {
                        return Err(format!("Type '{}' not found", id))
                    }
                };
                if remaining == 0 {
                    let b = id.to_string();
                    if ! self.env_type_fields.contains_key(&b) {
                        self.env_type_fields.insert(b,(0,Vec::new()));
                    }
                    Ok(None)
                } else {
                    Err(format!("Requested type '{}' has {} extra fields", id, depth))
                }
            },
            PicoIRIdentType::FieldName => {
                let (type_id, field_id)  = ExtName::prefix_and_tail_of_name(id);
                if let Some((ext_type,depth,v)) = self.toplevel.find_type_of_string(type_id) {
                    if v.len() == 0 {
                        match ext_type.get_field_index(field_id) {
                            None =>  {
                                return Err(format!("Type {} does not have field '{}' not found", type_id, field_id))
                            }
                            _ => ()
                        }
                        if !self.env_type_fields.contains_key(type_id) {
                            self.env_type_fields.insert(type_id.to_string(),(0,Vec::new()));
                        }
                        self.env_type_fields.get_mut(type_id).unwrap().1.push((field_id.to_string(),0));
                        Ok(None)
                    } else {
                        Err(format!("Field '{}' of type '{}' not found", field_id, type_id))
                    }
                } else {
                    return Err(format!("Type for field '{}' not found", type_id))
                }
            },
            PicoIRIdentType::StkAcc => {
                let (stack_depth, ident) = {
                    match id.find("@") {
                        None => (0, id),
                        Some(n) => {
                            let (ident, rest) = id.split_at(n);
                            let stack_depth = rest.split_at(1).1;
                            let stack_depth = isize::from_str_radix(stack_depth, 10).unwrap(); // Sort out the error case
                            (stack_depth, ident)
                        }
                    }
                };
                for (i,&n) in self.stack_env.iter().enumerate() {
                    if n == ident {
                        return Ok(Some(stack_depth - 1 - (i as isize)));
                    }
                }
                Err(format!("Stack does not contain '{}'", ident))
            },
            _ => Ok(None),
        }
    }
    //mi resolve_id
    fn resolve_id(&mut self, id_type:PicoIRIdentType, id:&str) -> PicoIRResolution {
        match id_type {
            PicoIRIdentType::EnvAcc => {
                if let Some((n,_)) = self.env_type_fields.get(id) {
                    Ok(Some(*n as isize))
                } else {
                    Ok(None)
                }
            },
            PicoIRIdentType::FieldName => {
                let (type_id, field_id)  = ExtName::prefix_and_tail_of_name(id);
                if let Some((_,v)) = self.env_type_fields.get(type_id) {
                    for (n,i) in v.iter() {
                        if n == field_id {
                            return Ok(Some(*i as isize));
                        }
                    }
                    Ok(None)
                } else {
                    Ok(None)
                }
            },
            _ => Ok(None),
        }
    }
    //mp resolve
    pub fn resolve(&mut self, program:&mut PicoIRProgram) -> PicoIRResolution {
        program.resolve(&mut |a,b| self.record_id(a,b))?;
        self.enumerate();
        program.resolve(&mut |a,b| self.resolve_id(a,b))?;
        println!("Disassembly:{}", program.disassemble());
        Ok(None)
    }
    //mp create_env
    pub fn create_env<H:PicoHeap<V>>(&self, interp_heap:&mut H) -> (V, Vec<&ExtType<Ob, Pl, V>>) {
        let env = interp_heap.alloc(PicoTag::Env as usize, self.num_types);
        let mut v = Vec::new();
        for (type_name, (env_index, fields)) in self.env_type_fields.iter() {
            let (ext_type,_,_) = self.toplevel.find_type_of_string(type_name).unwrap();
            let record = interp_heap.alloc(PicoTag::Record as usize, fields.len());
            for i in 0..fields.len() {
                let fn_number = ext_type.get_field_index(&fields[i].0).unwrap();
                let c = interp_heap.create_closure(0x80000000+env_index, vec![V::int(fn_number as isize)]);
                interp_heap.set_field(record, i, c);
            }
            interp_heap.set_field(env, *env_index, record);
            v.push(ext_type);
        }
        (env, v)
    }
}

