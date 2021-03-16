//a Imports
use std::rc::Rc;
use std::cell::RefCell;
use super::geometry::{Point, Bezier};
use super::polynomial::{Poly};

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
    pub fn clone(&self) -> Self {
        match self {
            Self::Bezier(b) => { Self::Bezier(b.clone()) },
            Self::Point(b) => { Self::Point(b.clone()) },
            Self::Poly(b) => { Self::Poly(b.clone()) },
        }
    }
    pub fn as_bezier(&self) -> RrcBezier {
        match &self { Object::Bezier(b) => { b.clone() },
                      _ => { panic!("Bad object type"); } }
    }
    pub fn as_point(&self) -> RrcPoint {
        match &self { Object::Point(p) => { p.clone() },
                      _ => { panic!("Bad object type"); } }
    }
    pub fn as_poly(&self) -> RrcPoly {
        match &self { Object::Poly(p) => { p.clone() },
                      _ => { panic!("Bad object type"); } }
    }
    pub fn of_point(pt:Point) -> Self {
        Object::Point(Rc::new(RefCell::new(pt)))
    }
    pub fn of_bezier(b:Bezier) -> Self {
        Object::Bezier(Rc::new(RefCell::new(b)))
    }
    pub fn of_poly(p:Poly) -> Self {
        Object::Poly(Rc::new(RefCell::new(p)))
    }
}
