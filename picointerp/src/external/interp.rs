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
use super::invocation::*;

//a ExtInterp
//tp ExtInterp
pub struct ExtInterp <'a, Ob, Pl:ExtObjectPool<Ob>, P:PicoProgram, V:PicoValue, H:PicoHeap<V>> {
    toplevel   : &'a ExtModule<Ob, Pl, V>,
    pub interp     : PicoInterp<'a, P, V, H>,
    inv        : &'a ExtInvocation<'a, Ob, Pl, V>,
    ext_types  : Vec<&'a ExtType<Ob, Pl, V>>,
    pool       : &'a mut Pl,
}

//ip ExtInterp
impl <'a, Ob, Pl:ExtObjectPool<Ob>, P:PicoProgram, V:PicoValue, H:PicoHeap<V>> ExtInterp<'a, Ob, Pl, P, V, H> {
    //fp new
    pub fn new(code:&'a P, toplevel:&'a ExtModule<Ob, Pl, V>, pc:usize, pool:&'a mut Pl, inv:&'a ExtInvocation<'a, Ob, Pl, V>) -> Self {
        let mut interp = PicoInterp::<'a, P, V, H>::new(code);
        let (env, ext_types) = inv.create_env(&mut interp.heap);
        interp.set_pc(pc);
        interp.set_env(env);
        Self { toplevel, interp, ext_types, inv, pool }
    }
    pub fn exec(&mut self) {
        let mut trace = PicoTraceStdout::new();
        loop {
            match self.interp.run_code(&mut trace, 100) {
                PicoExecCompletion::Completed(_) => { break; },
                PicoExecCompletion::External(pc) => {
                    let uid = pc ^ 0x80000000;
                    if uid >= self.ext_types.len() { panic!("External type id in closure outside the bounds" ); }
                    let c = self.interp.get_env(); // Should be the invoked closure
                    let fn_number = self.interp.heap.get_field(c, 1).as_usize();
                    let r = {
                        match self.ext_types[uid].invoke(fn_number, &mut self.pool, &mut self.interp.heap, &mut self.interp.stack) {
                            Ok(r) => r,
                            Err(s) => {panic!("Exec error {}",s);}
                        }
                    };
                    self.interp.ret(0, 0, r);
                },
                _ => { panic!("Unexpected result from run_code"); }
            }
        }
    }

}

