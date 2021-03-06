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

@file    pc_u8.rs
@brief   A packet bytecode representation
 */

//a Imports
use crate::{PicoTrace, PicoProgram, PicoValue, PicoStack};

//a PicoTraceStdout
pub struct PicoTraceStdout {
}
impl PicoTraceStdout {
    pub fn new() -> Self {
        Self { }
    }
}
impl PicoTrace for PicoTraceStdout {
    fn trace_fetch<P:PicoProgram>(&mut self, program:&P, pc:usize) -> bool {
        let instruction  = program.fetch_instruction(pc);
        println!("Fetch {}:{}",pc,instruction);
        false
    }
    fn trace_exec<F:FnOnce() -> String>(&mut self, trace_fn:F) {
        println!("Exec {}",&trace_fn());
    }
    fn trace_stack<V:PicoValue, S:PicoStack<V>>(&mut self, reason:&str, stack:&S, depth:usize) {
        println!("Stack {} : {}",reason, stack.as_str(depth));
    }
}

