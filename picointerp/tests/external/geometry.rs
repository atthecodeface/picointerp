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
use super::{Value, Object, ObjFn, ObjModule};

//a Geometry for test
/// Geometry types
//tp Point
pub type Point = (f32, f32);

//tp Bezier
pub struct Bezier { p0:Point, c:Point, p1:Point }

//ip Bezier - a quadrative bezier curve
impl Bezier {
    //fp new
    /// Create a new Bezier curve
    pub fn new(p0:Point, c:Point, p1:Point) -> Self {
        Self { p0, c, p1 }
    }

    //mp point_at
    /// Find the point at Bezier(t), for 0<= t <=1
    pub fn point_at(&self, t:f32) -> Point {
        let u = 1. - t;
        let x = u*u*self.p0.0 + 2.*u*t*self.c.0 + t*t*self.p1.0;
        let y = u*u*self.p0.1 + 2.*u*t*self.c.1 + t*t*self.p1.1;
        (x,y)
    }

    //mp direction_at
    /// Find the gradient of the Bezier at t, for 0<= t <=1
    pub fn direction_at(&self, t:f32) -> Point {
        let u = 1. - t;
        let x = t*self.p1.0 + (u-t)*self.c.0 + u*self.p0.0;
        let y = t*self.p1.1 + (u-t)*self.c.1 + u*self.p0.1;
        (x,y)
    }
    //zp All done
}

pub fn make_module<V:Value>(s:&str) -> ObjModule::<V> {
    let mut geometry = ObjModule::new(s);
    geometry.add_type(
        "bezier",
        vec![
            ("new",     ObjFn::OOOtO( Box::new(
                |_,p0,c,p1| Object::of_bezier(Bezier::new(p0.as_point().borrow().clone(),
                                                                 c.as_point().borrow().clone(),
                                                                 p1.as_point().borrow().clone()
                ))
            ))),
            ("p_of_t",  ObjFn::OItO( Box::new(
                |_,b,t| Object::of_point(b.as_bezier().borrow().point_at(V::as_float(t)))
            ))),
            ("dp_of_t", ObjFn::OItO( Box::new(
                |_,b,t| Object::of_point(b.as_bezier().borrow().direction_at(V::as_float(t)))
            ))),
        ]
    );
    geometry
}

