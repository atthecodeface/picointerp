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
use crate::ir::{PicoIRInstruction, PicoIRProgram, PicoIRIdentType};
use crate::base::{Opcode, ArithOp, LogicOp, CmpOp, BranchOp, AccessOp};

//a  

pub trait PicoBaseType : Sized {
    fn of_unit() -> Self;
    fn of_isize() -> Self;
    fn of_bool()  -> Self;
}

pub enum PicoType<B:PicoBaseType> {
    BaseType(B),
    Tuple(Vec<usize>), // Vec so it is ordered
    Record(Vec<(String, usize)>), // Vec so it is ordered
    TaggedUnion(Vec<(String, usize)>), // Vec so it is ordered
    Function(usize, usize),
    // Array(usize),
}

impl <B:PicoBaseType> PicoType<B> {
    pub fn new_base(base:B) -> Self {
        Self::BaseType(base)
    }
    pub fn new_tuple(fields:Vec<usize>) -> Self {
        Self::Tuple(fields)
    }
    pub fn new_record(field_names:Vec<&str>, field_types:Vec<usize>) -> Self {
        assert!(field_names.len() == field_types.len());
        let mut fields = Vec::new();
        for (n,v) in field_names.iter().zip(field_types.iter()) {
            fields.push( (n.to_string(), *v) );
        }
        Self::Record(fields)
    }
    pub fn new_tagged_union(tag_names:Vec<&str>, types:Vec<usize>) -> Self {
        assert!(tag_names.len() == types.len());
        let mut options = Vec::new();
        for (n,v) in tag_names.iter().zip(types.iter()) {
            options.push( (n.to_string(), *v) );
        }
        Self::TaggedUnion(options)
    }
    pub fn new_function(arg:usize, value:usize) -> Self {
        Self::Function(arg,value)
    }
    pub fn type_of_record_field(&self, name:&str) -> Option<usize> {
        match self {
            Self::Record(fields) => {
                for (n,t) in fields.iter() {
                    if n == name { return Some(*t); }
                }
                None
            },
            _ => None,
        }
    }
    pub fn type_of_enum(&self, name:&str) -> Option<usize> {
        match self {
            Self::TaggedUnion(fields) => {
                for (n,t) in fields.iter() {
                    if n == name { return Some(*t); }
                }
                None
            },
            _ => None,
        }
    }
    //pub fn iter_tags(&self) -> impl Iterator < Item = (&str, usize) > {
    //}
}

pub struct PicoTypeSet<B:PicoBaseType> {
    // Keep a vector as it needs to be ordered!
    types: Vec<(String, PicoType<B>)>,
    //
    scope_stack : Vec<String>,
}

impl <B:PicoBaseType> PicoTypeSet<B> {
    // type TypeReference : usize ;
    pub fn new() -> Self {
        let types       = Vec::new();
        let scope_stack = Vec::new();
        Self { types, scope_stack }
    }
    pub fn push_scope(&mut self, name:&str) {
        self.scope_stack.push(name.to_string());
    }
    pub fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }
    pub fn scope_name(&self) -> String {
        let mut r = String::new();
        for s in &self.scope_stack {
            if r.len() > 0 {
                r.push_str("::");
            }
            r.push_str(s);
        }
        r
    }
    pub fn add_type(&mut self, name:&str, pico_type:PicoType<B>) -> usize {
        let n = self.types.len();
        self.types.push( (name.to_string(), pico_type) );
        n
    }
    pub fn find_type(&self, name:&str) -> Option<usize> {
        for (i,(n,_)) in self.types.iter().enumerate() {
            if n == name {
                return Some(i);
            }
        }
        None
    }
}

//a Test
#[cfg(test)]
mod test_types {
    use super::*;
    enum BaseType {
        Unit,
        Bool,
        Int,
        Float,
    }

    impl PicoBaseType for BaseType {
        fn of_unit()  -> Self { BaseType::Unit }
        fn of_bool()  -> Self { BaseType::Bool }
        fn of_isize() -> Self { BaseType::Int }
    }

    type Type    = PicoType<BaseType>;
    type TypeSet = PicoTypeSet<BaseType>;

    fn create_types () -> TypeSet {
        let mut type_set   = TypeSet::new();
        let base_int     = type_set.add_type( "int",   Type::new_base(BaseType::Int) );
        let base_float   = type_set.add_type( "float", Type::new_base(BaseType::Float) );
        type_set.push_scope("diagram");
        type_set.push_scope("geometry");
        let point        = type_set.add_type( "point", Type::new_tuple(vec![base_float, base_float]) );
        let bbox         = type_set.add_type( "bbox",  Type::new_tuple(vec![point, point]) );
        type_set.pop_scope();
        type_set.push_scope("path");
        let path_element = type_set.add_type( "path_element", Type::new_record( vec!["flags", "width"], vec![base_int, base_float] ) );
        type_set.pop_scope();
        type_set.pop_scope();
        type_set
    }
    fn test() {
        let ts = create_types();
        assert_eq!(ts.find_type("not a type"),   None);
        assert_eq!(ts.find_type("int"),   Some(0));
        assert_eq!(ts.find_type("float"), Some(1));
    }
}

/*a Lambda play */
//it TLBinOp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TLBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Xor,
    Lsl,
    Lsr,
    Asr,
}
impl std::fmt::Display for TLBinOp {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "Add"),
            Self::Sub => write!(f, "Sub"),
            Self::Mul => write!(f, "Mul"),
            Self::Div => write!(f, "Div"),
            Self::Mod => write!(f, "Mod"),
            Self::And => write!(f, "And"),
            Self::Or => write!(f, "Or"),
            Self::Xor => write!(f, "Xor"),
            Self::Lsl => write!(f, "Lsl"),
            Self::Lsr => write!(f, "Lsr"),
            Self::Asr => write!(f, "Asr"),
        }
        
    }
}
//it TLUnOp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TLUnOp {
    BoolNot,
    Neg
}
impl std::fmt::Display for TLUnOp {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::BoolNot => write!(f, "BoolNot"),
            Self::Neg => write!(f, "Neg"),
        }
    }
}

//it TLCmpOp
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TLCmpOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Ult,
    Uge,
}
impl std::fmt::Display for TLCmpOp {
    //mp fmt - format for display
    /// Display in human-readble form
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Eq => write!(f, "Eq"),
            Self::Ne => write!(f, "Ne"),
            Self::Lt => write!(f, "Lt"),
            Self::Gt => write!(f, "Gt"),
            Self::Le => write!(f, "Le"),
            Self::Ge => write!(f, "Ge"),
            Self::Ult => write!(f, "Ult"),
            Self::Uge => write!(f, "Uge"),
        }
    }
}

//pt BTypedLambda
pub type BTypedLambda = Box<TypedLambda>;

//pt TypedLambda
pub enum TypedLambda  {
    /// Unary op is 'a -> 'a
    UnOp(TLUnOp,  BTypedLambda),
    /// Binary op is 'a -> 'a -> 'a
    BinOp(TLBinOp, BTypedLambda, BTypedLambda),
    /// Comparison op is 'a -> 'a -> bool
    CmpOp(TLCmpOp, BTypedLambda, BTypedLambda),
    /// Sequence is 'a -> 'b -> 'b
    Seq(BTypedLambda, BTypedLambda),
    /// Cond is bool -> 'a -> 'a -> 'a
    Cond(BTypedLambda, BTypedLambda, BTypedLambda),
    /// Call is ('a -> 'b) -> 'a -> 'b
    Call(BTypedLambda, BTypedLambda),
    /// Const
    ConstInt(isize),
    /// Access - access environment (be it stack in a sense or general environment)
    Access(String),
}

//ip TLInst
pub struct TLInst {
    pre_label  : Option<String>,
    post_label : Option<String>,
    inst  : PicoIRInstruction,
}
impl TLInst {
    pub fn new(opcode:Opcode) -> Self {
        Self {pre_label:None, post_label:None, inst:PicoIRInstruction::new(opcode)}
    }
    pub fn new_os(opcode:Opcode, subop:usize) -> Self {
        Self {pre_label:None, post_label:None, inst:PicoIRInstruction::make(Opcode::ArithOp, Some(subop), vec![], vec![])}
    }
    pub fn new_access(subop:AccessOp) -> Self {
        Self {pre_label:None, post_label: None, inst:PicoIRInstruction::make(Opcode::AccessOp, Some(subop as usize), vec![], vec![])}
    }
    pub fn new_arith(subop:ArithOp) -> Self {
        Self {pre_label:None, post_label: None, inst:PicoIRInstruction::make(Opcode::ArithOp, Some(subop as usize), vec![], vec![])}
    }
    pub fn new_logic(subop:LogicOp) -> Self {
        Self {pre_label:None, post_label: None, inst:PicoIRInstruction::make(Opcode::LogicOp, Some(subop as usize), vec![], vec![])}
    }
    pub fn new_cmp(subop:CmpOp) -> Self {
        Self {pre_label:None, post_label: None, inst:PicoIRInstruction::make(Opcode::IntCmp, Some(subop as usize), vec![], vec![])}
    }
    pub fn new_branch(subop:BranchOp) -> Self {
        Self {pre_label:None, post_label: None, inst:PicoIRInstruction::make(Opcode::Branch, Some(subop as usize), vec![], vec![])}
    }
    pub fn set_pre_label(&mut self, label:String)  {
        self.pre_label = Some(label);
    }
    pub fn set_post_label(&mut self, label:String)  {
        self.post_label = Some(label);
    }
    pub fn set_args_idents(mut self, args:Vec<isize>, idents:Vec<Option<(PicoIRIdentType, String)>> ) -> Self {
        self.inst.set_args_idents(args, idents);
        self
    }
}
//ip TypedLambda
impl TypedLambda {
    //fp new_un_op
    pub fn new_un_op(un_op:TLUnOp, l:Self) -> Self {
        Self::UnOp( un_op, Box::new(l) )
    }
    //fp new_bin_op
    pub fn new_bin_op(bin_op:TLBinOp, l:Self, r:Self) -> Self {
        Self::BinOp( bin_op, Box::new(l), Box::new(r) )
    }
    //fp new_cmp_op
    pub fn new_cmp_op(cmp_op:TLCmpOp, l:Self, r:Self) -> Self {
        Self::CmpOp( cmp_op, Box::new(l), Box::new(r) )
    }
    //fp new_seq
    pub fn new_seq(ls:Vec<Self>) -> Self {
        let mut be = None;
        for lambda in ls {
            match be {
                None =>     { be = Some(lambda); },
                Some(l) =>  { be = Some(Self::Seq(Box::new(l), Box::new(lambda))); },
            }
        }
        be.expect("Seq must have at least one entry")
    }

    //fp new_cond
    pub fn new_cond(c:Self, l:Self, r:Self) -> Self {
        Self::Cond( Box::new(c), Box::new(l), Box::new(r) )
    }
    //fp new_call
    pub fn new_call(func:Self, arg:Self) -> Self {
        Self::Call( Box::new(func), Box::new(arg) )
    }
    //fp new_access
    pub fn new_access(name:&str) -> Self {
        Self::Access( name.to_string() )
    }
    //mp as_str
    pub fn as_str(&self, indent:usize, mut acc:Vec<(usize, String)>) -> Vec<(usize, String) > {
        match self {
            Self::UnOp(o,l) => {
                acc.push((indent,format!("({}",o)));
                acc = l.as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::BinOp(o,l,r) => {
                acc.push((indent,format!("({}",o)));
                acc = l.as_str(indent+2,acc);
                acc = r.as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::CmpOp(o,l,r) => {
                acc.push((indent,format!("({}",o)));
                acc = l.as_str(indent+2,acc);
                acc = r.as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::Cond(c,l,r) => {
                acc.push((indent,format!("(cond")));
                acc = c.as_str(indent+2,acc);
                acc = l.as_str(indent+2,acc);
                acc = r.as_str(indent+2,acc);
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
                acc = func.as_str(indent+2,acc);
                acc = arg.as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
            Self::Seq(l,r) => {
                acc.push((indent,format!("(seq")));
                acc = l.as_str(indent+2,acc);
                acc = r.as_str(indent+2,acc);
                acc.push((indent,format!(")")));
            },
        }
        acc
    }
    //mp compile
    /// Compile a lambda to PicoIRInstructions, given a particular stack depth
    ///
    /// On exit the accumulator is assumed to be valid with the result of the lambda
    /// The rest of the stack is environment
    pub fn compile(&self, acc_valid: bool, depth:isize, uid:usize, is_end:bool) -> (isize, usize, Vec<TLInst>) {
        match self {
            Self::UnOp(o,l) => {
                let (new_depth, uid, mut inst) = l.compile(acc_valid, depth, uid, false);
                match o {
                    TLUnOp::BoolNot => { inst.push(TLInst::new_logic(LogicOp::BoolNot)); }
                    TLUnOp::Neg     => { inst.push(TLInst::new_arith(ArithOp::Neg)); }
                }
                (new_depth, uid, inst)
            },
            Self::BinOp(o,l,r) => {
                let (new_depth, uid, mut inst) = l.compile(acc_valid, depth, uid, false); // should push 0/1
                let (new_depth, uid, mut inst2) = r.compile(true, new_depth, uid, false);  // should push 1
                inst.extend(inst2);
                match o {
                    TLBinOp::Add => { inst.push(TLInst::new_arith(ArithOp::Add)); }
                    TLBinOp::Sub => { inst.push(TLInst::new_arith(ArithOp::Sub)); }
                    TLBinOp::Mul => { inst.push(TLInst::new_arith(ArithOp::Mul)); }
                    TLBinOp::Div => { inst.push(TLInst::new_arith(ArithOp::Div)); }
                    TLBinOp::Mod => { inst.push(TLInst::new_arith(ArithOp::Mod)); }
                    TLBinOp::And => { inst.push(TLInst::new_logic(LogicOp::And)); }
                    TLBinOp::Or =>  { inst.push(TLInst::new_logic(LogicOp::Or)); }
                    TLBinOp::Xor => { inst.push(TLInst::new_logic(LogicOp::Xor)); }
                    TLBinOp::Lsl => { inst.push(TLInst::new_logic(LogicOp::Lsl)); }
                    TLBinOp::Lsr => { inst.push(TLInst::new_logic(LogicOp::Lsr)); }
                    TLBinOp::Asr => { inst.push(TLInst::new_logic(LogicOp::Asr)); }
                }
                (new_depth-1, uid, inst)
            },
            Self::CmpOp(o,l,r) => {
                let (new_depth, uid, mut inst) = l.compile(acc_valid, depth, uid, false); // should push 0/1
                let (new_depth, uid, mut inst2) = r.compile(true, new_depth, uid, false);  // should push 1
                inst.extend(inst2);
                match o {
                    TLCmpOp::Eq  => { inst.push(TLInst::new_cmp(CmpOp::Eq)); }
                    TLCmpOp::Ne  => { inst.push(TLInst::new_cmp(CmpOp::Ne)); }
                    TLCmpOp::Lt  => { inst.push(TLInst::new_cmp(CmpOp::Lt)); }
                    TLCmpOp::Gt  => { inst.push(TLInst::new_cmp(CmpOp::Gt)); }
                    TLCmpOp::Le  => { inst.push(TLInst::new_cmp(CmpOp::Le)); }
                    TLCmpOp::Ge  => { inst.push(TLInst::new_cmp(CmpOp::Ge)); }
                    TLCmpOp::Ult => { inst.push(TLInst::new_cmp(CmpOp::Ult)); }
                    TLCmpOp::Uge => { inst.push(TLInst::new_cmp(CmpOp::Uge)); }
                }
                (new_depth-1, uid, inst)
            },
            Self::Cond(c,l,r) => {
                let (new_depth, uid, mut inst) = c.compile(acc_valid, depth, uid, false); // should push 0/1
                let (new_depth, uid, mut inst2) = l.compile(false, new_depth, uid, is_end);
                let (new_depth2, uid, mut inst3) = r.compile(false, new_depth, uid, is_end);
                assert!(new_depth == new_depth2);
                let label_if_true = format!("L{}",uid);
                let uid = uid + 1;
                inst.push(TLInst::new_branch(BranchOp::Ne).set_args_idents(vec![0], vec![Some((PicoIRIdentType::Branch,label_if_true.clone()))]));
                inst3[0].set_pre_label(label_if_true);
                if (!is_end) {
                    let label_rejoin = format!("L{}",uid);
                    let uid = uid + 1;
                    inst.push(TLInst::new_branch(BranchOp::Al).set_args_idents(vec![0], vec![Some((PicoIRIdentType::Branch,label_rejoin.clone()))]));
                    let n = inst3.len()-1;
                    inst3[n].set_post_label(label_rejoin);
                }
                inst.extend(inst2);
                inst.extend(inst3);
                (new_depth2, uid, inst)
            },
            Self::ConstInt(z) => {
                let mut inst = Vec::new();
                let subop = if acc_valid {AccessOp::PushConst} else {AccessOp::Const};
                inst.push(TLInst::new_access(subop).set_args_idents(vec![*z], vec![]));
                if is_end {
                    inst.push(TLInst::new(Opcode::Return).set_args_idents(vec![depth], vec![]));
                    (0, uid, inst)
                } else {
                    (depth+1, uid, inst)
                }
            },
            Self::Access(s) => {
                let mut inst = Vec::new();
                // is s on the stack? It is if it is in some kind of stack environment - then we need to resolve it here relative to stack depth
                let subop = if acc_valid {AccessOp::PushAcc} else {AccessOp::Acc};
                inst.push(TLInst::new_access(subop).set_args_idents(vec![0], vec![Some((PicoIRIdentType::EnvAcc,s.clone()))]));
                if is_end {
                    inst.push(TLInst::new(Opcode::Return).set_args_idents(vec![depth], vec![]));
                    (0, uid, inst)
                } else {
                    (depth+1, uid, inst)
                }
            },
            Self::Call(func,arg) => {
                let (new_depth, uid, mut inst) = arg.compile(acc_valid, depth, uid, false); // should push 0/1, leaves acc_valid
                let (new_depth, uid, mut inst2) = func.compile(true, new_depth+1, uid, false); // should push 0/1, leaves acc_valid
                inst.extend(inst2);
                inst.push(TLInst::new(Opcode::ApplyN).set_args_idents(vec![1], vec![]));
                if is_end {
                    inst.push(TLInst::new(Opcode::Return).set_args_idents(vec![depth], vec![]));
                    (0, uid, inst)
                } else {
                    (depth+1, uid, inst)
                }
            },
            Self::Seq(l,r) => {
                (depth, uid, vec![])
            },
        }
    }
    //zz All done
}

//a Test
#[cfg(test)]
mod test_lambdas {
    use super::*;
    enum BaseType {
        Unit,
        Int,
        Float,
    }
    #[test]
    fn test() {
        let factorial =
            TypedLambda::new_cond(
                TypedLambda::new_cmp_op(
                    TLCmpOp::Gt,
                    TypedLambda::new_access("n"),
                    TypedLambda::ConstInt(1),
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
            );
        let mut v = Vec::new();
        let v = factorial.as_str(0,v);
        for (ind,s) in v {
            println!("{}",s);
        }
        let (depth,uid,inst) = factorial.compile(false, 0, 0, true); // acc_valid, depth, uid, is_end
        let mut program = PicoIRProgram::new();
        for i in inst {
            if let Some(l) = i.pre_label  {
                program.add_label(l);
            }
            program.add_instruction(i.inst);
            if let Some(l) = i.post_label  {
                program.add_label(l);
            }
        }
        program.resolve(&|_,_| None);
        println!("{}", program.disassemble());
        assert!(false);
    }
}    

