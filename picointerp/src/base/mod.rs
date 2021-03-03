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

@file    base/mod.rs
@brief   Base picointerpreter library
 */

//a Imports and exports

mod types;
mod interpreter;

pub use self::types::{PicoProgram, PicoTrace, PicoCode, PicoValue, PicoStack, PicoHeap, PicoTag, PicoExecCompletion};

pub use self::types::{Opcode, ArithOp, LogicOp, CmpOp, BranchOp, AccessOp};

pub use self::interpreter::PicoInterp;

