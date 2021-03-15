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

@file    external/mod.rs
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

//a External stuff
//em ExtName
pub mod ExtName {
    pub fn split_name<'a> (s:&'a str) -> Vec<&'a str> {
        s.split("::").collect()
    }
    pub fn prefix_and_tail_of_name<'a> (s:&'a str) -> (&'a str, &'a str) {
        let v : Vec<&str> = s.rsplitn(2,"::").collect();
        match v.len() {
            1 => ("", v[0]),
            2 => (v[1], v[0]),
            _ => panic!("Bug in string library")
        }
    }
    pub fn cut_name<'a> (s:&'a str, n:usize) -> (&'a str, &'a str) {
        if n == 0 {
            ("", s)
        } else {
            let mut i = 0;
            for (p,_) in s.match_indices("::") {
                i += 1;
                if i == n {
                    let (root, rest) = s.split_at(p);
                    let (_, tail) = rest.split_at(2);
                    return (root, tail)
                }
            }
            (s, "")
        }
    }
}

