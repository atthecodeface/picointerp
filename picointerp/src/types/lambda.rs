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

//a Constants
const DEBUG_COMPILE : bool = (1 == 1);

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
            Self::Or  => write!(f, "Or"),
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

//pt TLInst
#[derive(Debug)]
pub struct TLInst {
    pre_label  : Option<String>,
    post_label : Option<String>,
    inst  : PicoIRInstruction,
}

//ip TLInst
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
//ti TLCompilation
#[derive(Debug, Clone, Copy, PartialEq)]
enum TLCompEndState {
    /// Not the end of the function - do not insert a Ret
    NotEnd,
    /// Last step - insert a Ret on the end of this, or tail-recursion if desired
    LastStep,
    /// End handled - a child has already handled the Ret
    EndHandled,
}

#[derive(Debug)]
struct TLCompilation {
    // add stack environment undo
    stack_depth: isize, // Depth of stack AFTER code
    acc_valid  : bool,  // Asserted if accumulator is valid - this is for internal checks, as it should be statically correct
    uid        : usize, // Increasing uid used for label generation; guaranteed to be >= uid on entry to code compilation
    end_state  : TLCompEndState,  // Asserted if this compilation completes the function
    inst       : Vec<TLInst>, // Instructions that the code has been compiled into
}

//ii TLCompilation
impl TLCompilation {
    //fp new
    pub fn new() -> Self {
        let stack_depth = 0;
        let acc_valid = false;
        let uid = 0;
        let inst = Vec::new();
        let end_state = TLCompEndState::NotEnd;
        Self {stack_depth, acc_valid, uid, end_state, inst}
    }
    //mp push
    pub fn push(&self) -> Self {
        if DEBUG_COMPILE { println!("Push {} {} {} {:?}", self.stack_depth, self.acc_valid, self.uid, self.end_state ); }
        Self { stack_depth:self.stack_depth, acc_valid:self.acc_valid, uid:self.uid, end_state:self.end_state, inst:Vec::new() }
    }
    //mp is_end
    pub fn is_end(&self) -> bool {
        self.end_state == TLCompEndState::LastStep
    }
    //cp set_end
    pub fn set_end(mut self, is_end:bool) -> Self {
        self.end_state = if is_end { TLCompEndState::LastStep } else { TLCompEndState::NotEnd };
        self
    }
    //cp set_uid
    pub fn set_uid(mut self, other:&Self) -> Self {
        self.uid = other.uid;
        self
    }
    //mp get_label
    pub fn get_label(&mut self) -> String {
        let label = format!("L{}",self.uid);
        self.uid += 1;
        if DEBUG_COMPILE { println!("Got label {}", label); }
        label
    }
    //fp pre_label
    pub fn pre_label(&mut self, label:String) {
        if DEBUG_COMPILE { println!("Prelabel with {}", label); }
        self.inst[0].set_pre_label(label);
    }
    //fp post_label
    pub fn post_label(&mut self, label:String) {
        if DEBUG_COMPILE { println!("Postlabel with {}", label); }
        let n = self.inst.len()-1;
        self.inst[n].set_post_label(label);
    }
    //mp push_inst
    pub fn push_inst(&mut self, inst:TLInst) {
        if DEBUG_COMPILE { println!("Push {:?}", inst); }
        self.inst.push(inst);
    }
    //mp extend
    pub fn extend(&mut self, other:Self) {
        if DEBUG_COMPILE { println!("Extend with {:?}", other.inst); }
        if DEBUG_COMPILE { println!("   acc_valid {} stack_depth {} uid {}", other.acc_valid, other.stack_depth, other.uid ); }
        self.uid = other.uid;
        self.acc_valid = other.acc_valid;
        self.stack_depth = other.stack_depth;
        self.inst.extend(other.inst);
    }
    //cp handle_end
    pub fn handle_end(mut self) -> Self {
        if DEBUG_COMPILE { println!("Handle end {} {} {:?}", self.acc_valid, self.stack_depth, self.end_state ); }
        assert!(self.acc_valid, "Acc must be valid for end of function - it is the result");
        if self.end_state == TLCompEndState::LastStep {
            self.push_inst(TLInst::new(Opcode::Return).set_args_idents(vec![self.stack_depth], vec![]));
            self.stack_depth = 0;
            self.end_state = TLCompEndState::EndHandled;
        }
        self
    }
    //cp end_already_handled
    pub fn end_already_handled(mut self) -> Self {
        if DEBUG_COMPILE { println!("End already handled {} {} {:?}", self.acc_valid, self.stack_depth, self.end_state ); }
        self
    }
    //cp compile_lambda
    /// Compile a lambda to PicoIRInstructions, given a particular stack depth
    ///
    /// On exit the accumulator is assumed to be valid with the result of the lambda
    /// The rest of the stack is environment
    pub fn compile(mut self, lambda:&TypedLambda) -> Self {
        match lambda {
            //cs UnOp
            TypedLambda::UnOp(o,l) => {
                let l_frame = self.push().set_end(false).compile(l);
                self.extend(l_frame);
                assert!(self.acc_valid, "Acc must be valid for unary op");
                match o {
                    TLUnOp::BoolNot => { self.push_inst(TLInst::new_logic(LogicOp::BoolNot)); }
                    TLUnOp::Neg     => { self.push_inst(TLInst::new_arith(ArithOp::Neg)); }
                }
                assert!(self.acc_valid, "Acc must be valid after unary op");
                self.handle_end()
            },
            //cs BinOp
            TypedLambda::BinOp(o,l,r) => {
                let l_frame = self.push().set_end(false).compile(l);
                let r_frame = l_frame.push().compile(r);
                self.extend(l_frame);
                self.extend(r_frame);
                assert!(self.acc_valid, "Acc must be valid for binary op");
                match o {
                    TLBinOp::Add => { self.push_inst(TLInst::new_arith(ArithOp::Add)); }
                    TLBinOp::Sub => { self.push_inst(TLInst::new_arith(ArithOp::Sub)); }
                    TLBinOp::Mul => { self.push_inst(TLInst::new_arith(ArithOp::Mul)); }
                    TLBinOp::Div => { self.push_inst(TLInst::new_arith(ArithOp::Div)); }
                    TLBinOp::Mod => { self.push_inst(TLInst::new_arith(ArithOp::Mod)); }
                    TLBinOp::And => { self.push_inst(TLInst::new_logic(LogicOp::And)); }
                    TLBinOp::Or =>  { self.push_inst(TLInst::new_logic(LogicOp::Or)); }
                    TLBinOp::Xor => { self.push_inst(TLInst::new_logic(LogicOp::Xor)); }
                    TLBinOp::Lsl => { self.push_inst(TLInst::new_logic(LogicOp::Lsl)); }
                    TLBinOp::Lsr => { self.push_inst(TLInst::new_logic(LogicOp::Lsr)); }
                    TLBinOp::Asr => { self.push_inst(TLInst::new_logic(LogicOp::Asr)); }
                }
                self.stack_depth -= 1;
                assert!(self.acc_valid, "Acc must be valid after binary op");
                self.handle_end()
            },
            //cs CmpOp
            TypedLambda::CmpOp(o,l,r) => {
                let l_frame = self.push().set_end(false).compile(l);
                let r_frame = l_frame.push().compile(r);
                self.extend(l_frame);
                self.extend(r_frame);
                assert!(self.acc_valid, "Acc must be valid for compare op");
                match o {
                    TLCmpOp::Eq  => { self.push_inst(TLInst::new_cmp(CmpOp::Eq)); }
                    TLCmpOp::Ne  => { self.push_inst(TLInst::new_cmp(CmpOp::Ne)); }
                    TLCmpOp::Lt  => { self.push_inst(TLInst::new_cmp(CmpOp::Lt)); }
                    TLCmpOp::Gt  => { self.push_inst(TLInst::new_cmp(CmpOp::Gt)); }
                    TLCmpOp::Le  => { self.push_inst(TLInst::new_cmp(CmpOp::Le)); }
                    TLCmpOp::Ge  => { self.push_inst(TLInst::new_cmp(CmpOp::Ge)); }
                    TLCmpOp::Ult => { self.push_inst(TLInst::new_cmp(CmpOp::Ult)); }
                    TLCmpOp::Uge => { self.push_inst(TLInst::new_cmp(CmpOp::Uge)); }
                }
                self.stack_depth -= 1;
                assert!(self.acc_valid, "Acc must be valid after binary op");
                self.handle_end()
            },
            //cs Cond
            TypedLambda::Cond(c,l,r) => {
                let mut c_frame = self.push().set_end(false).compile(c);

                let label_if_true = c_frame.get_label();
                c_frame.push_inst(TLInst::new_branch(BranchOp::Ne).set_args_idents(vec![0], vec![Some((PicoIRIdentType::Branch,label_if_true.clone()))]));
                let c_frame = c_frame; // Drop mutability for safety
                
                let mut l_frame = c_frame.push().set_end(self.is_end()).compile(l);
                let label_rejoin = {
                    if self.is_end() {
                        None
                    } else {
                        let label_rejoin = l_frame.get_label();
                        l_frame.push_inst(TLInst::new_branch(BranchOp::Al).set_args_idents(vec![0], vec![Some((PicoIRIdentType::Branch,label_rejoin.clone()))]));
                        Some(label_rejoin)
                    }
                };
                let l_frame = l_frame; // Drop mutability for safety

                let mut r_frame = c_frame.push().set_end(self.is_end()).set_uid(&l_frame).compile(r);
                assert_eq!(l_frame.stack_depth, r_frame.stack_depth, "Resultant stack depth of two branches of a conditional must be the same");

                r_frame.pre_label(label_if_true);
                
                self.extend(c_frame);
                self.extend(l_frame);
                self.extend(r_frame);
                if let Some(label_rejoin) = label_rejoin {
                    self.post_label(label_rejoin);
                }
                // Note that the end will already have been handled by the l or r lambda's
                self.end_already_handled()
            },
            //cs ConstInt
            TypedLambda::ConstInt(z) => {
                let (subop, stack_delta) = if self.acc_valid {(AccessOp::PushConst,1)} else {(AccessOp::Const,0)};
                self.push_inst(TLInst::new_access(subop).set_args_idents(vec![*z], vec![]));
                self.stack_depth += stack_delta;
                self.acc_valid = true;
                self.handle_end()
            },
            //cs Access
            TypedLambda::Access(s) => {
                // is s on the stack? It is if it is in some kind of stack environment - then we need to resolve it here relative to stack depth
                let (subop, stack_delta) = if self.acc_valid {(AccessOp::PushAcc,1)} else {(AccessOp::Acc,0)};
                self.push_inst(TLInst::new_access(subop).set_args_idents(vec![0], vec![Some((PicoIRIdentType::EnvAcc,s.clone()))]));
                self.stack_depth += stack_delta;
                self.acc_valid = true;
                self.handle_end()
            },
            //cs Call
            TypedLambda::Call(func,arg) => {
                let arg_frame  = self.push().set_end(false).compile(arg);
                let func_frame = arg_frame.push().set_end(false).compile(func);
                self.extend(arg_frame);
                self.extend(func_frame);
                self.push_inst(TLInst::new(Opcode::ApplyN).set_args_idents(vec![1], vec![]));
                // Apply of 1 has 1 argument on the stack, and afterwards that has been removed in result is in acc
                self.stack_depth -= 1;
                self.acc_valid = true;
                self.handle_end()
            },
            //cs Seq
            TypedLambda::Seq(l,r) => {
                self
            },
            //cs All done
        }
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
        let mut compilation = TLCompilation::new().set_end(true);
        compilation = compilation.compile(&factorial);
        let mut program = PicoIRProgram::new();
        for i in compilation.inst {
            if let Some(l) = i.pre_label  {
                program.add_label(l);
            }
            program.add_instruction(i.inst);
            if let Some(l) = i.post_label  {
                program.add_label(l);
            }
        }
        program.resolve(&|a,b| {println!("{}({})",a,b);None} );
        println!("{}", program.disassemble());
        assert!(false);
    }
}    

