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

mod name;
mod function;
mod types;
mod module;
mod invocation;
mod interp;

pub use self::name::ExtName;
pub use self::function::{ExtFn, ExtObjectPool};
pub use self::types::ExtType;
pub use self::module::ExtModule;
pub use self::invocation::ExtInvocation;
pub use self::interp::ExtInterp;

