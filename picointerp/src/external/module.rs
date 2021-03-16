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
use crate::{PicoValue};
use crate::{ExtName, ExtFn, ExtType, ExtObjectPool};

//a ExtModule
//tp ExtModule
#[derive(Debug)]
pub struct ExtModule<Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> {
    name       : String,
    submodules : Vec<ExtModule<Ob, Pl, V>>,
    types      : Vec<(String,ExtType<Ob, Pl, V>)>,
}

//pi ExtModule
impl <Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtModule<Ob, Pl, V> {
    pub fn new(name:&str) -> Self {
        let name = name.to_string();
        Self {name,
              submodules : Vec::new(),
              types      : Vec::new(),
        }
    }
    pub fn add_module(&mut self, module:Self) {
        self.submodules.push(module);
    }
    pub fn add_type(&mut self, name:&str, fns:Vec<(&str, ExtFn<Ob, Pl, V>)>) {
        let ext_type = ExtType::of_fns(fns);
        self.types.push((name.to_string(), ext_type));
    }
    pub fn find_module_of_string<'a> (&'a self, s:&'a str) -> (&'a Self, usize, Vec<&'a str>) {
        self.find_module_of_path(0, ExtName::split_name(s))
    }
    pub fn find_type_of_string<'a> (&'a self, s:&'a str) -> Option<(&'a ExtType<Ob, Pl, V>, usize, Vec<&'a str>)> {
        self.find_type_of_path(ExtName::split_name(s))
    }
    pub fn find_module_of_path<'a> (&'a self, depth:usize, mut v:Vec<&'a str>) -> (&'a Self, usize, Vec<&'a str>) {
        match v.len() {
            0 => (self, depth, v),
            _ => {
                for m in &self.submodules {
                    if v[0] == m.name {
                        v.remove(0);
                        return m.find_module_of_path(depth+1, v);
                    }
                }
                (self, depth, v)
            }
        }
    }
    pub fn find_type_of_path<'a> (&'a self, v:Vec<&'a str>) -> Option<(&'a ExtType<Ob, Pl, V>, usize, Vec<&'a str>)> {
        let (m, d, v) = self.find_module_of_path(0, v);
        m.find_type(d, v)
    }
    pub fn find_type<'a> (&'a self, depth:usize, mut v:Vec<&'a str>) -> Option<(&'a ExtType<Ob, Pl, V>, usize, Vec<&'a str>)> {
        match v.len() {
            0 => { None }
            _ => {
                for (n,ref t) in &self.types {
                    if v[0] == n {
                        v.remove(0);
                        return Some((t, depth, v))
                    }
                }
                None
            }
        }
    }
}
