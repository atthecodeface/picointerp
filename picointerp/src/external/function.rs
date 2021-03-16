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
use crate::{PicoValue, PicoHeap, PicoStack};

//a pt ExtObjectPool
pub trait ExtObjectPool<Ob> {
    fn add_obj(&mut self, obj:Ob) -> u32;
    fn get_obj(&mut self, handle:u32) -> Option<Ob>;
}

//a ExtFn
//tp ExtFn
// ExtFn is a base type or a vec of traits?
// Trait is a set of functions of N arguments
pub enum ExtFn<Ob, Pl:ExtObjectPool<Ob>, V> {
    /// Function Obj -> Obj -> Obj -> Obj
    OOOtO(  Box<dyn Fn(&mut Pl,Ob,Ob,Ob) -> Ob> ),
    /// Function Obj -> V
    OtI(    Box<dyn Fn(&mut Pl,Ob) -> V> ),
    /// Function Obj -> V -> Obj
    OItO(   Box<dyn Fn(&mut Pl,Ob,V) -> Ob> ),
    /// Function Obj -> V -> V
    OItI(   Box<dyn Fn(&mut Pl,Ob,V) -> V> ),
    /// Method Obj -> V -> (), returning self
    OItS(   Box<dyn Fn(&mut Pl,Ob,V) -> ()> ),
    /// Method Obj -> V -> V -> (), returning self
    OIItS(  Box<dyn Fn(&mut Pl,Ob,V,V) -> ()> ),
    /// Function Obj -> Obj -> Obj
    OOtO(   Box<dyn Fn(&mut Pl,Ob,Ob) -> Ob> ),
}

//ip ExtFn
impl <Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtFn<Ob, Pl, V> {
    //mp invoke
    pub fn invoke<H:PicoHeap<V>, S:PicoStack<V>>(&self, pool:&mut Pl, _interp_heap:&mut H, interp_stack:&mut S) -> Result<V,String> {
        match self {
            Self::OtI(f) => {
                if let Some(o) = pool.get_obj(interp_stack.pop().as_usize() as u32) {
                    Ok(f(pool, o))
                } else { Err(format!("Could not get object")) }
            }
            Self::OItS(f) => {
                let v = interp_stack.pop();
                let obj = interp_stack.pop();
                if let Some(o) = pool.get_obj(obj.as_usize() as u32) {
                    f(pool, o, v);
                    Ok(obj)
                } else { Err(format!("Could not get object")) }
            }
            Self::OIItS(f) => {
                let v1 = interp_stack.pop();
                let v0 = interp_stack.pop();
                let obj = interp_stack.pop();
                if let Some(o) = pool.get_obj(obj.as_usize() as u32) {
                    f(pool, o, v0, v1);
                    Ok(obj)
                } else { Err(format!("Could not get object")) }
            }
            Self::OItI(f) => {
                let v = interp_stack.pop();
                let obj = interp_stack.pop();
                if let Some(o) = pool.get_obj(obj.as_usize() as u32) {
                    Ok(f(pool, o, v))
                } else { Err(format!("Could not get object")) }
            }
            Self::OOtO(f) => {
                let obj1 = interp_stack.pop();
                let obj0 = interp_stack.pop();
                if let Some(o0) = pool.get_obj(obj0.as_usize() as u32) {
                    if let Some(o1) = pool.get_obj(obj1.as_usize() as u32) {
                        let obj = f(pool, o0, o1);
                        Ok(V::int(pool.add_obj(obj) as isize))
                    } else { Err(format!("Could not get object")) }
                } else { Err(format!("Could not get object")) }
            }
            _ => {
                    Err(format!("Not yet implemented"))
            }
        }
    }
    //zz All done
}
