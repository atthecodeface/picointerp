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

@file    geometry.rs
@brief   Simple geometry types for external tests
 */

//a Imports
extern crate picointerp;
use picointerp::PicoValue;
pub trait Value: PicoValue {
    fn as_float(t:Self) -> f32 {
        t.as_isize() as f32 / 1000.0
    }
    fn of_float(f:f32) -> Self {
        Self::int((f * 1000.0).round() as isize)
    }
}

