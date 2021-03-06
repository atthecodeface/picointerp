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

//a PicoTraceNone
pub struct PicoTraceNone {
}
impl PicoTraceNone {
    pub fn new() -> Self {
        Self { }
    }
}
impl PicoTrace for PicoTraceNone {
    fn trace_fetch<P:PicoProgram>(&mut self, _program:&P, _pc:usize) -> bool { false }
    fn trace_exec<F:FnOnce() -> String>(&mut self, _trace_fn:F) {}
    fn trace_stack<V:PicoValue, S:PicoStack<V>>(&mut self, _reason:&str, _stack:&S, _depth:usize) {}
}

