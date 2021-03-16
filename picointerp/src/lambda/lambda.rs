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

@file    mode.rs
@brief   types
 */

//a Imports
use super::lambda_op::{TLUnOp, TLBinOp, TLCmpOp};

//a Constants
// const DEBUG_LAMBDA : bool = 1 == 1;

//a TypedLambda
//pt BTypedLambda
/// A boxed version is used as a TypedLambda is owned by its parent in
/// the expression, but it need to be some form of reference; a box
/// beats out a borrowed reference which would need to be owned
/// somewhere else
pub trait TLTypeRef : Sized + std::fmt::Debug {
    fn of_unit() -> Self;
}
pub struct BTypedLambda<T:TLTypeRef> {
    t   : T,
    btl : Box<TypedLambda<T>>,
}
impl <T:TLTypeRef> BTypedLambda<T> {
    pub fn of_tl(tl:TypedLambda<T>) -> Self {
        Self { t:T::of_unit(), btl:Box::new(tl) }
    }
    pub fn borrow_tl(&self) -> &TypedLambda<T> {
        &self.btl
    }
}

//pt TypedLambda
pub enum TypedLambda<T:TLTypeRef>  {
    /// Func is String -> Vec<String, 'a[i]> -> 'a[0] -> 'a[1] -> ... -> 'b
    Func(String, Vec<(String,T)>, BTypedLambda<T>),
    /// Unary op is 'a -> 'a
    UnOp(TLUnOp,  BTypedLambda<T>),
    /// Binary op is 'a -> 'a -> 'a
    BinOp(TLBinOp, BTypedLambda<T>, BTypedLambda<T>),
    /// Comparison op is 'a -> 'a -> bool
    CmpOp(TLCmpOp, BTypedLambda<T>, BTypedLambda<T>),
    /// Sequence is '_ -> '_ -> ... -> 'b -> 'b
    Seq(Vec<BTypedLambda<T>>),
    /// Cond is bool -> 'a -> 'a -> 'a
    Cond(BTypedLambda<T>, BTypedLambda<T>, BTypedLambda<T>),
    /// Call is ('a -> 'b) -> 'a -> 'b
    Call(BTypedLambda<T>, BTypedLambda<T>),
    /// Const
    ConstInt(isize),
    /// Access - access environment (be it stack in a sense or general environment)
    Access(String),
    /// Let x : 'a = x_expr : 'a in l : 'b -> 'b
    Let(String,T, BTypedLambda<T>, BTypedLambda<T>),
}

//ip TypedLambda
impl <T:TLTypeRef> TypedLambda<T> {
    //fp boxed
    pub fn boxed(self) -> BTypedLambda<T> {
        BTypedLambda::of_tl(self)
    }
    //fp new_func
    pub fn new_func(name:&str, args:Vec<&str>, l:Self) -> Self {
        let name = name.to_string();
        let args = args.iter().map(|x| (x.to_string(),T::of_unit())).collect();
        Self::Func( name, args, l.boxed() )
    }
    //fp new_let
    pub fn new_let(name:&str, v:Self, l:Self) -> Self {
        let name = name.to_string();
        Self::Let( name, T::of_unit(), v.boxed(), l.boxed() )
    }
    //fp new_un_op
    pub fn new_un_op(un_op:TLUnOp, l:Self) -> Self {
        Self::UnOp( un_op, l.boxed() )
    }
    //fp new_bin_op
    pub fn new_bin_op(bin_op:TLBinOp, l:Self, r:Self) -> Self {
        Self::BinOp( bin_op, l.boxed(), r.boxed() )
    }
    //fp new_cmp_op
    pub fn new_cmp_op(cmp_op:TLCmpOp, l:Self, r:Self) -> Self {
        Self::CmpOp( cmp_op, l.boxed(), r.boxed() )
    }
    //fp new_seq
    pub fn new_seq(ls:Vec<Self>) -> Self {
        let mut be = Vec::new();
        for l in ls {
            be.push(l.boxed());
        }
        Self::Seq( be )
    }

    //fp new_cond
    pub fn new_cond(c:Self, l:Self, r:Self) -> Self {
        Self::Cond( c.boxed(), l.boxed(), r.boxed() )
    }
    //fp new_call
    pub fn new_call(func:Self, arg:Self) -> Self {
        Self::Call( func.boxed(), arg.boxed() )
    }
    //fp new_access
    pub fn new_access(name:&str) -> Self {
        Self::Access( name.to_string() )
    }
    //mp as_str
    pub fn as_str(&self, indent:usize, mut acc:Vec<(usize, String)>) -> Vec<(usize, String) > {
        match self {
            Self::Func(name, args, l) => {
                acc.push((indent,format!("(func {} {:?}",name, args)));
                acc = l.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::Let(name, _t, v, l) => {
                acc.push((indent,format!("(let {}",name)));
                acc = v.borrow_tl().as_str(indent+2,acc);
                acc = l.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::UnOp(o,l) => {
                acc.push((indent,format!("({}",o)));
                acc = l.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::BinOp(o,l,r) => {
                acc.push((indent,format!("({}",o)));
                acc = l.borrow_tl().as_str(indent+2,acc);
                acc = r.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::CmpOp(o,l,r) => {
                acc.push((indent,format!("({}",o)));
                acc = l.borrow_tl().as_str(indent+2,acc);
                acc = r.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::Cond(c,l,r) => {
                acc.push((indent,format!("(cond")));
                acc = c.borrow_tl().as_str(indent+2,acc);
                acc = l.borrow_tl().as_str(indent+2,acc);
                acc = r.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::ConstInt(z) => {
                acc.push((indent,format!("{}",z)));
            },
            Self::Access(s) => {
                acc.push((indent,format!("env.{}",s)));
            },
            Self::Call(func,arg) => {
                acc.push((indent,format!("(call")));
                acc = func.borrow_tl().as_str(indent+2,acc);
                acc = arg.borrow_tl().as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::Seq(v) => {
                acc.push((indent,format!("(seq")));
                for l in v {
                    acc = l.borrow_tl().as_str(indent+2,acc);
                }
                acc.push((indent,format!(")")));
            },
        }
        acc
    }
    //zz All done
}

//a Test
#[cfg(test)]
pub mod test_lambdas {
    use super::*;
    #[derive(Debug)]
    enum BaseType {
        Unit,
        Int,
        Float,
    }
    impl TLTypeRef for BaseType {
        fn of_unit() -> Self { Self::Unit }
    }
    pub fn factorial_lambda<T:TLTypeRef>() -> TypedLambda<T> {
        TypedLambda::<T>::new_seq(
            vec![
                TypedLambda::new_let(
                    "factorial",
                    TypedLambda::new_func(
                        "factorial", vec!["n", "acc"],
                        TypedLambda::new_cond(
                            TypedLambda::new_cmp_op(
                                TLCmpOp::Gt,
                                TypedLambda::ConstInt(1),
                                TypedLambda::new_access("n"),
                            ),
                            TypedLambda::new_call(
                                TypedLambda::new_call(
                                    TypedLambda::new_access("factorial"),
                                    TypedLambda::new_bin_op(
                                        TLBinOp::Mul,
                                        TypedLambda::new_access("acc"),
                                        TypedLambda::new_access("n")
                                    ),
                                ),
                                TypedLambda::new_bin_op(
                                    TLBinOp::Add,
                                    TypedLambda::ConstInt(-1),
                                    TypedLambda::new_access("n"),
                                ),
                            ),
                            TypedLambda::new_access("acc"),
                        ),
                    ),
                    TypedLambda::new_call(
                        TypedLambda::new_call(
                            TypedLambda::new_access("factorial"),
                            TypedLambda::ConstInt(1),
                        ),
                        TypedLambda::ConstInt(10),
                    ),
                ),
            ]
        )
    }
    #[test]
    fn test() {
        let v = Vec::new();
        let v = factorial_lambda::<BaseType>().as_str(0,v);
        for (_ind,s) in v {
            println!("{}",s);
        }
    }
}

