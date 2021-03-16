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

@file    polynomial.rs
@brief   Simple polynomial types for external tests
 */

//a Imports
extern crate picointerp;
use super::{Value, Object, ObjFn, ObjModule};

//a Polynomial
pub struct Poly {
    coeffs: Vec<f32>,
}
impl Poly {
    pub fn new() -> Self {
        Self { coeffs:Vec::new() }
    }
    pub fn scale(&mut self, scale:f32) {
        for i in 0..self.coeffs.len() {
            self.coeffs[i] *= scale;
        }
    }
    pub fn order(&self) -> isize {
        self.coeffs.len() as isize
    }
    pub fn get(&self, n:isize) -> f32 {
        let n = n as usize;
        if n >= self.coeffs.len() { 0.} else { self.coeffs[n] }
    }
    pub fn set(&mut self, n:isize, v:f32) {
        let n = n as usize;
        while n >= self.coeffs.len() {
            self.coeffs.push(0.);
        }
        self.coeffs[n] = v;
        println!("{}",self);
    }
    pub fn multiply(&self, other:&Self) -> Self {
        let sl = self.coeffs.len();
        let ol = other.coeffs.len();
        let n = sl * ol;
        let mut v = Vec::with_capacity(n);
        for _ in 0..n { v.push(0.); }
        for si in 0..sl {
            for oi in 0..ol {
                v[si+oi] += self.coeffs[si] * other.coeffs[oi];
            }
        }
        Self { coeffs:v }
    }
}
impl std::fmt::Display for Poly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for a in &self.coeffs {
            write!(f,"{}  ",a)?;
        }
        Ok(())
    }
}
pub fn make_module<V:Value>(s:&str) -> ObjModule<V> {
    let mut polynomial = ObjModule::new(s);
    polynomial.add_type(
        "poly",
        vec![
            ("order",    ObjFn::OtI(  Box::new(
                |_,p|     V::int(p.as_poly().borrow().order())
            ))),
            ("get",    ObjFn::OItI(  Box::new(
                |_,p,n|   V::of_float(p.as_poly().borrow().get(n.as_isize()))
            ))),
            ("set",    ObjFn::OIItS(  Box::new(
                |_,p,n,v|   p.as_poly().borrow_mut().set(n.as_isize(),V::as_float(v))
            ))),
            ("scale",    ObjFn::OItS( Box::new(
                |_,p,t|   p.as_poly().borrow_mut().scale(V::as_float(t))
            ))),
            ("multiply", ObjFn::OOtO( Box::new(
                |_,p0,p1| Object::of_poly(p0.as_poly().borrow().multiply(&p1.as_poly().borrow()))
            ))),
        ]
    );
    polynomial
}
