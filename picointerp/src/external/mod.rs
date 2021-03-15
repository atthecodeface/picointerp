//a Imports
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use crate::{PicoInterp, PicoProgram, PicoTrace, PicoValue, PicoHeap, PicoStack, PicoTag, PicoExecCompletion};
use crate::{PicoTraceStdout};
use crate::{PicoProgramU32};
use crate::{PicoIRAssembler, PicoIREncoding, PicoIRProgram, PicoIRIdentType, PicoIRResolution};

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

pub trait ExtObjectPool<Ob> {
    fn add_obj(&mut self, obj:Ob) -> u32;
    fn get_obj(&mut self, handle:u32) -> Option<Ob>;
}

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

//a External stuff
//em ExtName
mod ExtName {
    pub fn split_name<'a> (s:&'a str) -> Vec<&'a str> {
        s.split("::").collect()
    }
    pub fn prefix_and_tail_of_name<'a> (s:&'a str) -> (&'a str, &'a str) {
        let v : Vec<&str> = s.rsplitn(2,"::").collect();
        match v.len() {
            1 => ("", v[0]),
            2 => (v[1], v[0]),
            _ => panic!("Bug in string library")
        }
    }
    pub fn cut_name<'a> (s:&'a str, n:usize) -> (&'a str, &'a str) {
        if n == 0 {
            ("", s)
        } else {
            let mut i = 0;
            for (p,_) in s.match_indices("::") {
                i += 1;
                if i == n {
                    let (root, rest) = s.split_at(p);
                    let (_, tail) = rest.split_at(2);
                    return (root, tail)
                }
            }
            (s, "")
        }
    }
}

//tp ExtFn
// ExtFn is a base type or a vec of traits?
// Trait is a set of functions of N arguments
pub enum ExtFn<Ob, Pl:ExtObjectPool<Ob>, V> {
    OOOtO(  Box<dyn Fn(&mut Pl,Ob,Ob,Ob) -> Ob> ),
    OtI(    Box<dyn Fn(&mut Pl,Ob) -> V> ),
    OItO(   Box<dyn Fn(&mut Pl,Ob,V) -> Ob> ),
    OItI(   Box<dyn Fn(&mut Pl,Ob,V) -> V> ),
    OItS(   Box<dyn Fn(&mut Pl,Ob,V) -> ()> ),
    OIItS(  Box<dyn Fn(&mut Pl,Ob,V,V) -> ()> ),
    OOtO(   Box<dyn Fn(&mut Pl,Ob,Ob) -> Ob> ),
}

impl <Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtFn<Ob, Pl, V> {
    pub fn invoke<H:PicoHeap<V>, S:PicoStack<V>>(&self, pool:&mut Pl, interp_heap:&mut H, interp_stack:&mut S) -> Result<V,String> {
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
}
//tp ExtType
pub struct ExtType<Ob, Pl:ExtObjectPool<Ob>, V> {
    fns : Vec<(String, ExtFn<Ob, Pl, V>)>,
}
impl <Ob, Pl:ExtObjectPool<Ob>, V> std::fmt::Debug for ExtType<Ob, Pl, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"Type[")?;
        for (n,_) in &self.fns {
            write!(f,"<Fn {}> ",n)?;
        }
        write!(f,"]")
    }
}
//pi ExtType
impl <Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtType<Ob, Pl, V> {
    //mp get_field_index
    pub fn get_field_index(&self, s:&str) -> Option<usize> {
        for (i,(n,_)) in self.fns.iter().enumerate() {
            if n == s { return Some(i) }
        }
        None
    }
    //mp invoke
    pub fn invoke<H:PicoHeap<V>, S:PicoStack<V>>(&self, fn_number:usize, pool:&mut Pl, interp_heap:&mut H, interp_stack:&mut S) -> Result<V,String> {
        if fn_number >= self.fns.len() {
            Err(format!("Function number {} out of range", fn_number))
        } else {
            self.fns[fn_number].1.invoke(pool, interp_heap, interp_stack)
        }
    }
    //fp of_fns
    pub fn of_fns( fns:Vec<(&str,ExtFn<Ob, Pl, V>)> ) -> Self {
        let mut v = Vec::new();
        for (n,f) in fns {
            v.push( (n.to_string(),f) );
        }
        Self { fns:v }
    }
    //mp invoke_closure
    pub fn invoke_closure<H:PicoHeap<V>, S:PicoStack<V>> (&self, index:usize, handle:V, interp_heap:&mut H, interp_stack:&mut S,) -> V {
        let x = interp_stack.pop();
        println!("Evaluate {} * {}",x.as_isize(), handle.as_isize());
        let r = V::int(x.as_isize() * handle.as_isize());
        r
    }
    //mp interp_create_closures_for_instance
    pub fn interp_create_closures_for_instance<H:PicoHeap<V>>(&self, interp_heap:&mut H, handle:V) -> Vec<V> {
        let mut v = Vec::new();
        for i in 0..self.fns.len() {
            v.push( interp_heap.create_closure(0x80000000+i, vec![handle]) );
        }
        v
    }
    //mp interp_create_type_record_for_instance
    pub fn interp_create_type_record_for_instance<H:PicoHeap<V>>(&self, interp_heap:&mut H, handle:V) -> V {
        let record = interp_heap.alloc(PicoTag::Record as usize, self.fns.len());
        let v = self.interp_create_closures_for_instance(interp_heap, handle);
        let mut n = 0;
        for c in v {
            interp_heap.set_field(record, n, c);
            n += 1;
        }
        record
    }
}

//tp ExtModule
#[derive(Debug)]
pub struct ExtModule<Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> {
    name       : String,
    submodules : Vec<ExtModule<Ob, Pl, V>>,
    types      : Vec<(String,ExtType<Ob, Pl, V>)>,
}

//pi ExtModule
impl <Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtModule<Ob, Pl, V> {
    pub fn new(name:&str) -> Self {
        let name = name.to_string();
        Self {name,
              submodules : Vec::new(),
              types      : Vec::new(),
        }
    }
    pub fn add_module(&mut self, module:Self) {
        self.submodules.push(module);
    }
    pub fn add_type(&mut self, name:&str, fns:Vec<(&str, ExtFn<Ob, Pl, V>)>) {
        let ext_type = ExtType::of_fns(fns);
        self.types.push((name.to_string(), ext_type));
    }
    pub fn find_module_of_string<'a> (&'a self, s:&'a str) -> (&'a Self, usize, Vec<&'a str>) {
        self.find_module_of_path(0, ExtName::split_name(s))
    }
    pub fn find_type_of_string<'a> (&'a self, s:&'a str) -> Option<(&'a ExtType<Ob, Pl, V>, usize, Vec<&'a str>)> {
        self.find_type_of_path(ExtName::split_name(s))
    }
    pub fn find_module_of_path<'a> (&'a self, depth:usize, mut v:Vec<&'a str>) -> (&'a Self, usize, Vec<&'a str>) {
        match v.len() {
            0 => (self, depth, v),
            _ => {
                for m in &self.submodules {
                    if v[0] == m.name {
                        v.remove(0);
                        return m.find_module_of_path(depth+1, v);
                    }
                }
                (self, depth, v)
            }
        }
    }
    pub fn find_type_of_path<'a> (&'a self, mut v:Vec<&'a str>) -> Option<(&'a ExtType<Ob, Pl, V>, usize, Vec<&'a str>)> {
        let (m, d, v) = self.find_module_of_path(0, v);
        m.find_type(d, v)
    }
    pub fn find_type<'a> (&'a self, depth:usize, mut v:Vec<&'a str>) -> Option<(&'a ExtType<Ob, Pl, V>, usize, Vec<&'a str>)> {
        match v.len() {
            0 => { None }
            _ => {
                for (n,ref t) in &self.types {
                    if v[0] == n {
                        v.remove(0);
                        return Some((t, depth, v))
                    }
                }
                None
            }
        }
    }
    //mp interp_create_module
    pub fn interp_create_module<H:PicoHeap<V>>(&self, interp_heap:&mut H, handle:V) {
        let env = interp_heap.alloc(PicoTag::Module as usize, self.types.len());
        for (i,(_,x)) in self.types.iter().enumerate() {
            let f = x.interp_create_type_record_for_instance(interp_heap, handle);
            interp_heap.set_field(env, i, f);
        }
    }
}
//tp Path
pub type Path = Vec<String>;

//a InvTypeIter
//tp InvTypeIter
/// An iterator over the types used in the invocation
///
pub struct InvTypeIter<'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue>  {
    invocation : &'a ExtInvocation<'a, Ob, Pl, V>,
    hash_iter  : std::collections::hash_map::Iter<'a, String, (usize,Vec<(String,usize)>)>,
    ext_type_fields   : Option<(&'a ExtType<Ob, Pl, V>, &'a Vec<(String, usize)>)>,
    field_index : usize,
}

//pi InvTypeIter
impl <'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> InvTypeIter<'a, Ob, Pl, V>  {
    //fp new
    pub fn new(invocation:&'a ExtInvocation<'a, Ob, Pl, V>) -> Self {
        let hash_iter = invocation.env_type_fields.iter();
        Self { invocation, hash_iter, ext_type_fields:None, field_index:0 }
    }

    //zz All done
}

//ip Iterator for InvTypeIter
impl <'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> Iterator for InvTypeIter<'a, Ob, Pl, V> {
    /// Item is a pair of points that make a straight line
    type Item = (&'a ExtType<Ob, Pl, V> , usize);
    //mp next
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((t,f)) = self.ext_type_fields {
            if let Some((field,_)) = f.get(self.field_index) {
                let n = t.get_field_index(&field).unwrap();
                self.field_index += 1;
                Some((t, n))
            } else {
                self.ext_type_fields = None;
                self.next()
            }
        } else {
            match self.hash_iter.next() {
                None => None,
                Some((type_name, field_names)) => {
                    let ext_type = self.invocation.toplevel.find_type_of_string(type_name).unwrap().0;
                    self.ext_type_fields = Some((ext_type, &field_names.1));
                    self.field_index = 0;
                    self.next()
                }
            }
        }
    }

    //zz All done
}

//a ExtInvocation
//tp ExtInvocation
pub struct ExtInvocation<'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> {
    toplevel        : &'a ExtModule<Ob, Pl, V>,
    stack_env       : Vec<&'a str>,
    env_type_fields : HashMap::<String,(usize,Vec<(String,usize)>)>,
    num_types       : usize
}

//ip ExtInvocation
impl <'a, Ob, Pl:ExtObjectPool<Ob>, V:PicoValue> ExtInvocation<'a, Ob, Pl, V> {
    //fp new
    /// Create a new invocation environment
    pub fn new(toplevel:&'a ExtModule<Ob, Pl, V>, stack_env:Vec<&'a str>) -> Self {
        let env_type_fields = HashMap::new();
        Self { toplevel, stack_env, env_type_fields, num_types:0 }
    }
    //mp enumerate
    /// Once the required types and fields are recorded, enumerate them
    pub fn enumerate(&mut self) {
        let mut index = 0;
        for (_, (ref mut n, fields)) in self.env_type_fields.iter_mut() {
            *n = index;
            index += 1;
            for (i, ref mut f) in fields.iter_mut().enumerate() {
                f.1 = i;
            }
        }
        self.num_types = index;
        println!("Enumerated {} types",self.num_types);
        println!("{:?}",self.env_type_fields);
    }
    //mp iter_env
    pub fn iter_env<'z>(&'z self) -> InvTypeIter<'z, Ob, Pl, V> {
        InvTypeIter::new(self)
    }
    //mp record_id
    fn record_id(&mut self, id_type:PicoIRIdentType, id:&str) -> PicoIRResolution {
        match id_type {
            PicoIRIdentType::EnvAcc => {
                let (depth, remaining) = {
                    if let Some((_,depth,v)) = self.toplevel.find_type_of_string(id) {
                        (depth, v.len())
                    } else {
                        return Err(format!("Type '{}' not found", id))
                    }
                };
                if remaining == 0 {
                    let b = id.to_string();
                    if ! self.env_type_fields.contains_key(&b) {
                        self.env_type_fields.insert(b,(0,Vec::new()));
                    }
                    Ok(None)
                } else {
                    Err(format!("Requested type '{}' has {} extra fields", id, depth))
                }
            },
            PicoIRIdentType::FieldName => {
                let (type_id, field_id)  = ExtName::prefix_and_tail_of_name(id);
                if let Some((ext_type,depth,v)) = self.toplevel.find_type_of_string(type_id) {
                    if v.len() == 0 {
                        match ext_type.get_field_index(field_id) {
                            None =>  {
                                return Err(format!("Type {} does not have field '{}' not found", type_id, field_id))
                            }
                            _ => ()
                        }
                        if !self.env_type_fields.contains_key(type_id) {
                            self.env_type_fields.insert(type_id.to_string(),(0,Vec::new()));
                        }
                        self.env_type_fields.get_mut(type_id).unwrap().1.push((field_id.to_string(),0));
                        Ok(None)
                    } else {
                        Err(format!("Field '{}' of type '{}' not found", field_id, type_id))
                    }
                } else {
                    return Err(format!("Type for field '{}' not found", type_id))
                }
            },
            PicoIRIdentType::StkAcc => {
                let (stack_depth, ident) = {
                    match id.find("@") {
                        None => (0, id),
                        Some(n) => {
                            let (ident, rest) = id.split_at(n);
                            let stack_depth = rest.split_at(1).1;
                            let stack_depth = isize::from_str_radix(stack_depth, 10).unwrap(); // Sort out the error case
                            (stack_depth, ident)
                        }
                    }
                };
                for (i,&n) in self.stack_env.iter().enumerate() {
                    if n == ident {
                        return Ok(Some(stack_depth - 1 - (i as isize)));
                    }
                }
                Err(format!("Stack does not contain '{}'", ident))
            },
            _ => Ok(None),
        }
    }
    //mi resolve_id
    fn resolve_id(&mut self, id_type:PicoIRIdentType, id:&str) -> PicoIRResolution {
        match id_type {
            PicoIRIdentType::EnvAcc => {
                if let Some((n,_)) = self.env_type_fields.get(id) {
                    Ok(Some(*n as isize))
                } else {
                    Ok(None)
                }
            },
            PicoIRIdentType::FieldName => {
                let (type_id, field_id)  = ExtName::prefix_and_tail_of_name(id);
                if let Some((_,v)) = self.env_type_fields.get(type_id) {
                    for (n,i) in v.iter() {
                        if n == field_id {
                            return Ok(Some(*i as isize));
                        }
                    }
                    Ok(None)
                } else {
                    Ok(None)
                }
            },
            _ => Ok(None),
        }
    }
    //mp resolve
    pub fn resolve(&mut self, program:&mut PicoIRProgram) -> PicoIRResolution {
        program.resolve(&mut |a,b| self.record_id(a,b))?;
        self.enumerate();
        program.resolve(&mut |a,b| self.resolve_id(a,b))?;
        println!("Disassembly:{}", program.disassemble());
        Ok(None)
    }
    //mp create_env
    pub fn create_env<H:PicoHeap<V>>(&self, interp_heap:&mut H) -> (V, Vec<&ExtType<Ob, Pl, V>>) {
        let env = interp_heap.alloc(PicoTag::Env as usize, self.num_types);
        let mut v = Vec::new();
        for (type_name, (env_index, fields)) in self.env_type_fields.iter() {
            let (ext_type,_,_) = self.toplevel.find_type_of_string(type_name).unwrap();
            let record = interp_heap.alloc(PicoTag::Record as usize, fields.len());
            for i in 0..fields.len() {
                let fn_number = ext_type.get_field_index(&fields[i].0).unwrap();
                let c = interp_heap.create_closure(0x80000000+env_index, vec![V::int(fn_number as isize)]);
                interp_heap.set_field(record, i, c);
            }
            interp_heap.set_field(env, *env_index, record);
            v.push(ext_type);
        }
        (env, v)
    }
}

//tp ExtInterp
pub struct ExtInterp <'a, Ob, Pl:ExtObjectPool<Ob>, P:PicoProgram, V:PicoValue, H:PicoHeap<V>> {
    toplevel   : &'a ExtModule<Ob, Pl, V>,
    interp     : PicoInterp<'a, P, V, H>,
    inv        : &'a ExtInvocation<'a, Ob, Pl, V>,
    ext_types  : Vec<&'a ExtType<Ob, Pl, V>>,
    pool       : &'a mut Pl,
}

//ip ExtInterp
impl <'a, Ob, Pl:ExtObjectPool<Ob>, P:PicoProgram, V:PicoValue, H:PicoHeap<V>> ExtInterp<'a, Ob, Pl, P, V, H> {
    //fp new
    pub fn new(code:&'a P, toplevel:&'a ExtModule<Ob, Pl, V>, pc:usize, pool:&'a mut Pl, inv:&'a ExtInvocation<'a, Ob, Pl, V>) -> Self {
        let mut interp = PicoInterp::<'a, P, V, H>::new(code);
        let (env, ext_types) = inv.create_env(&mut interp.heap);
        interp.set_pc(pc);
        interp.set_env(env);
        Self { toplevel, interp, ext_types, inv, pool }
    }
    pub fn exec(&mut self) {
        let mut trace = PicoTraceStdout::new();
        loop {
            match self.interp.run_code(&mut trace, 100) {
                PicoExecCompletion::Completed(_) => { break; },
                PicoExecCompletion::External(pc) => {
                    let uid = pc ^ 0x80000000;
                    if uid >= self.ext_types.len() { panic!("External type id in closure outside the bounds" ); }
                    let c = self.interp.get_env(); // Should be the invoked closure
                    let fn_number = self.interp.heap.get_field(c, 1).as_usize();
                    let r = {
                        match self.ext_types[uid].invoke(fn_number, &mut self.pool, &mut self.interp.heap, &mut self.interp.stack) {
                            Ok(r) => r,
                            Err(s) => {panic!("Exec error {}",s);}
                        }
                    };
                    self.interp.ret(0, 0, r);
                },
                _ => { panic!("Unexpected result from run_code"); }
            }
        }
    }

}

//a Test
//mt Test for PicoProgramU32
#[cfg(test)]
mod test_picoprogram_u32 {
    use super::*;
    use crate::base::{Opcode, ArithOp, AccessOp}; //, LogicOp, CmpOp, BranchOp};
    use crate::{PicoTraceStdout};
    use crate::PicoInterp;
    use crate::{PicoValue, PicoHeap, PicoStack, PicoTag, PicoExecCompletion};
    use crate::PicoIRAssembler;
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
