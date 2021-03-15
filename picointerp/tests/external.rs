//a Imports
extern crate picointerp;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use picointerp::{PicoInterp, PicoProgram, PicoTrace, PicoValue, PicoHeap, PicoStack, PicoTag, PicoExecCompletion};
use picointerp::{PicoTraceStdout};
use picointerp::{PicoProgramU32};
use picointerp::{PicoIRAssembler, PicoIREncoding, PicoIRProgram, PicoIRIdentType, PicoIRResolution};
use picointerp::{ExtName, ExtFn, ExtType, ExtModule, ExtInvocation, ExtInterp, ExtObjectPool};

//a Geometry for test
/// Geometry types
pub type Point = (f32, f32);
pub struct Bezier { p0:Point, c:Point, p1:Point }
impl Bezier {
    pub fn new(p0:Point, c:Point, p1:Point) -> Self {
        Self { p0, c, p1 }
    }
    pub fn point_at(&self, t:f32) -> Point {
        let u = 1. - t;
        let x = u*u*self.p0.0 + 2.*u*t*self.c.0 + t*t*self.p1.0;
        let y = u*u*self.p0.1 + 2.*u*t*self.c.1 + t*t*self.p1.1;
        (x,y)
    }
    pub fn direction_at(&self, t:f32) -> Point {
        let u = 1. - t;
        let x = t*self.p1.0 + (u-t)*self.c.0 + u*self.p0.0;
        let y = t*self.p1.1 + (u-t)*self.c.1 + u*self.p0.1;
        (x,y)
    }
}

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

//a Pool for test
pub type RrcBezier = Rc<RefCell<Bezier>>;
pub type RrcPoint  = Rc<RefCell<Point>>;
pub type RrcPoly   = Rc<RefCell<Poly>>;

pub enum Object {
    Bezier(RrcBezier),
    Point(RrcPoint),
    Poly(RrcPoly),
}

impl Object {
    fn clone(&self) -> Self {
        match self {
            Self::Bezier(b) => { Self::Bezier(b.clone()) },
            Self::Point(b) => { Self::Point(b.clone()) },
            Self::Poly(b) => { Self::Poly(b.clone()) },
        }
    }
    fn as_bezier(&self) -> RrcBezier {
        match &self { Object::Bezier(b) => { b.clone() },
                      _ => { panic!("Bad object type"); } }
    }
    fn as_point(&self) -> RrcPoint {
        match &self { Object::Point(p) => { p.clone() },
                      _ => { panic!("Bad object type"); } }
    }
    fn as_poly(&self) -> RrcPoly {
        match &self { Object::Poly(p) => { p.clone() },
                      _ => { panic!("Bad object type"); } }
    }
    fn of_point(pt:Point) -> Self {
        Object::Point(Rc::new(RefCell::new(pt)))
    }
    fn of_bezier(b:Bezier) -> Self {
        Object::Bezier(Rc::new(RefCell::new(b)))
    }
    fn of_poly(p:Poly) -> Self {
        Object::Poly(Rc::new(RefCell::new(p)))
    }
}

pub struct Pool {
    objs: Vec<Object>, // could be a hash if we delete objects, but no requirement here
}

impl Pool {
    pub fn new() -> Self {
        Self { objs: Vec::new() }
    }
    fn bezier_of_obj(&mut self, handle:u32) -> RrcBezier {
        if handle as usize >= self.objs.len() { panic!("Out of range handle"); }
        match &self.objs[handle as usize] {
            Object::Bezier(b) => { b.clone() },
            _ => { panic!("Bad object type"); }
        }
    }
}
impl ExtObjectPool<Object> for Pool {
    fn add_obj(&mut self, obj:Object) -> u32 {
        let n = self.objs.len();
        self.objs.push(obj);
        n as u32
    }
    fn get_obj(&mut self, handle:u32) -> Option<Object> {
        self.objs.get(handle as usize).map(|o| o.clone())
    }
}

//tp Path
pub type Path = Vec<String>;

//a Test
//mt Test for PicoProgramU32
#[cfg(test)]
mod test_picoprogram_u32 {
    use super::*;
    use picointerp::{PicoTraceStdout};
    use picointerp::PicoInterp;
    use picointerp::{PicoValue, PicoHeap, PicoStack, PicoTag, PicoExecCompletion};
    use picointerp::PicoIRAssembler;
    type Interp<'a> = ExtInterp::<'a, Object, Pool, PicoProgramU32, isize, Vec<isize>>;
    type Module = ExtModule::<Object, Pool, isize>;
    fn float_of_int(t:isize) -> f32 { t.as_isize() as f32 / 1000.0 }
    fn int_of_float(f:f32) -> isize { isize::int((f*1000.0).round() as isize) }
    #[test]
    fn test_ext() {
        let mut geometry = Module::new("Geometry");
        geometry.add_type(
            "bezier",
            vec![
                ("new",     ExtFn::OOOtO( Box::new(
                    |mut pool,p0,c,p1| Object::of_bezier(Bezier::new(p0.as_point().borrow().clone(),
                                                                     c.as_point().borrow().clone(),
                                                                     p1.as_point().borrow().clone()
                    ))
                ))),
                ("p_of_t",  ExtFn::OItO( Box::new(
                    |mut pool,b,t| Object::of_point(b.as_bezier().borrow().point_at(float_of_int(t)))
                ))),
                ("dp_of_t", ExtFn::OItO( Box::new(
                    |mut pool,b,t| Object::of_point(b.as_bezier().borrow().direction_at(float_of_int(t)))
                ))),
            ]
        );

        let mut polynomial = Module::new("Polynomial");
        polynomial.add_type(
            "poly",
            vec![
                ("order",    ExtFn::OtI(  Box::new(
                    |mut pool,p|     p.as_poly().borrow().order()
                ))),
                ("get",    ExtFn::OItI(  Box::new(
                    |mut pool,p,n|   int_of_float(p.as_poly().borrow().get(n.as_isize()))
                ))),
                ("set",    ExtFn::OIItS(  Box::new(
                    |mut pool,p,n,v|   p.as_poly().borrow_mut().set(n.as_isize(),float_of_int(v))
                ))),
                ("scale",    ExtFn::OItS( Box::new(
                    |mut pool,p,t|   p.as_poly().borrow_mut().scale(float_of_int(t))
                ))),
                ("multiply", ExtFn::OOtO( Box::new(
                    |mut pool,p0,p1| Object::of_poly(p0.as_poly().borrow().multiply(&p1.as_poly().borrow()))
                ))),
            ]
        );

        let mut toplevel = Module::new("Toplevel");
        toplevel.add_module(geometry);
        toplevel.add_module(polynomial);

        let mut assem = PicoIRAssembler::new();
        // invocation do_summat_two_ps : mut p0 p1 -> p0
        //  Polynomial::poly -> record
        let mut pico_ir = assem.parse("
             pushret -1
             acc p0@5
             pcnst 3
             pcnst 1234
             peacc Polynomial::poly
             fldget Polynomial::poly::set
             appn 3
             acc p0@5
             pcnst 2000
             peacc Polynomial::poly
             fldget Polynomial::poly::scale
             appn 2
             ret 0
        ").unwrap();

        let mut p0 = Poly::new();
        let mut p1 = Poly::new();

        let env_stack = vec!["p0", "p1"];
        let mut inv = ExtInvocation::new(&toplevel, env_stack);
        inv.resolve(&mut pico_ir).unwrap();
        for (t,n) in inv.iter_env() {
            println!("{:?},{}",t,n);
        }
        assert!(pico_ir.is_resolved());

        let mut code  = PicoProgramU32::new();
        code.of_program(&pico_ir).unwrap();

        for (i,n) in code.program.iter().enumerate() {
            println!("{} : {:08x}", i, n);
        }

        let mut pool = Pool::new();
        let p0 = pool.add_obj(Object::of_poly(p0));
        let p1 = pool.add_obj(Object::of_poly(p1));
        let mut interp = Interp::new(&code, &toplevel, 0, &mut pool, &inv);
        interp.interp.stack.push( isize::of_usize(p0 as usize) );
        interp.interp.stack.push( isize::of_usize(p1 as usize) );
        interp.exec();

        println!("p0 {}",pool.get_obj(p0).unwrap().as_poly().borrow());
        println!("p1 {}",pool.get_obj(p1).unwrap().as_poly().borrow());
        // assert_eq!(interp.get_accumulator(),isize::int(200));
        assert!(false);
    }
}
