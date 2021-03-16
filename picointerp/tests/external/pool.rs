extern crate picointerp;
use picointerp::{ExtFn, ExtModule};

use super::{Object, RrcBezier};

pub type ObjFn<V>     = ExtFn<Object, Pool, V>;
pub type ObjModule<V> = ExtModule<Object, Pool, V>;

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
impl picointerp::ExtObjectPool<Object> for Pool {
    fn add_obj(&mut self, obj:Object) -> u32 {
        let n = self.objs.len();
        self.objs.push(obj);
        n as u32
    }
    fn get_obj(&mut self, handle:u32) -> Option<Object> {
        self.objs.get(handle as usize).map(|o| o.clone())
    }
}

