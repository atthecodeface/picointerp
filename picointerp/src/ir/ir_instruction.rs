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

@file    ir_instruction.rs
@brief   PicoIRInstruction type and implementation
 */

//a Imports
use crate::base::{PicoProgram};
use crate::base::{Opcode};
use super::assemble::{Assembler};

//a LabelPool
#[derive(Debug)]
struct LabelPool (Vec<(String, usize)>);
impl LabelPool {
    //fp new
    pub fn new() -> Self {
        Self (Vec::new())
    }

    //mp get_label_index
    pub fn get_label_index(&self, s:&str) -> Option<usize> {
        for (label, index) in &self.0 {
            if s == label { return Some (*index) ; }
        }
        None
    }
    
    //mp add_label_at_index
    /// Add a new label with a given index
    pub fn add_label_at_index(&mut self, label:String, index:usize) {
        self.0.push( (label, index) );
    }

    //zz All done
}

//a PicoIRIdentType, PicoIRResolveFn
//pt IdentType
/// Used for instructions as target labels and labels for opcodes,
/// essentially prior to assembly and linking
///
/// Not required for general intepretation of code, but in the library
/// to have a common strucuture to support linking.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PicoIRIdentType {
    EnvAcc,
    StkAcc,
    Integer,
    FieldName,
    BlkTag,
    Branch,
    OffCl,
}

//a PicoIRInstruction
//pt PicoIRInstruction
#[derive(Debug)]
struct Resolvable {resolved:bool, id_type:PicoIRIdentType, id_string:String}

#[derive(Debug)]
pub struct PicoIRInstruction {
    pub opcode     : Opcode,
    pub subop      : Option<usize>,
    pub args       : Vec<isize>,
    labels         : Vec<Option<usize>>,
    idents         : Vec<Option<Resolvable>>,
}

//ip PicoIRInstruction
impl PicoIRInstruction {
    //fp new
    pub fn new(opcode:Opcode) -> Self {
        Self {
            opcode,
            subop  : None,
            args   : Vec::new(),
            labels : Vec::new(),
            idents : Vec::new(),
        }
    }

    //fp make
    pub fn make(opcode:Opcode, subop:Option<usize>, args:Vec<isize>, idents:Vec<Option<(PicoIRIdentType, String)>> ) -> Self {
        let mut resolvables = Vec::new();
        for ots in idents {
            resolvables.push( ots.map( |(id_type, id_string)| Resolvable { resolved:false, id_type, id_string } ) );
        }
        let mut elf = Self::new(opcode);
        elf.subop  = subop;
        elf.args   = args;
        elf.idents = resolvables;
        elf.labels = Vec::with_capacity(elf.args.len());
        for _ in &elf.args {elf.labels.push(None);}
        elf
    }

    //mp disassemble
    pub fn disassemble(&self)  -> String {
        let mut r = Assembler::opcode_str(self.opcode).to_string();
        if let Some(subop) = self.subop {
            match self.opcode {
                Opcode::ArithOp   => { r = Assembler::arithop_opcode_str(subop).to_string(); }
                Opcode::LogicOp   => { r = Assembler::logicop_opcode_str(subop).to_string(); }
                Opcode::IntCmp    => { r = Assembler::cmpop_opcode_str(subop).to_string(); }
                Opcode::IntBranch => { r = format!("b{}",Assembler::cmpop_opcode_str(subop)); }
                Opcode::AccessOp  => { r = Assembler::accessop_opcode_str(subop).to_string(); }
                _                 => { r = Assembler::branchop_opcode_str(subop).to_string(); }
            }
        }
        for i in 0..self.args.len() {
            let a = &self.args[i];
            r.push_str( &format!(" {:?}", a) );
            if  i < self.labels.len() {
                if let Some(ref l) = self.labels[i] {
                    r.push_str( &format!("#{}",l) );
                }
            }
            if  i < self.idents.len() {
                if let Some(ref id) = self.idents[i] {
                    r.push_str( &format!("@({}:{})", id.resolved, id.id_string) );
                }
            }
        }
        r
    }
    //mp resolve
    fn resolve<F:Fn(PicoIRIdentType, &str) -> Option<isize>>(&mut self, labels:&LabelPool, f:&F) -> bool {
        let mut is_resolved = true;
        for (i,id) in self.idents.iter_mut().enumerate() {
            match id {
                Some( Resolvable { ref mut resolved, id_type, id_string} )=>
                    if ! *resolved {
                        if *id_type == PicoIRIdentType::Branch {
                            if let Some(label_id) = labels.get_label_index(&id_string) {
                                self.labels[i] = Some(label_id);
                                *resolved = true;
                            } else {
                                is_resolved = false;
                            }
                        } else if let Some(arg) = f(*id_type, id_string) {
                            *resolved = true;
                            self.args[i] = arg;
                        } else {
                            is_resolved = false;
                        }
                    },
                None => (),
            }
        }
        is_resolved
    }

    //mp is_resolved
    pub fn is_resolved(&self) -> bool {
        for id in &self.idents {
            if let Some(resolvable) = id {
                if !resolvable.resolved { return false; }
            }
        }
        true
    }

    //mp remap_branch_args
    pub fn remap_branch_args<'a, F:Fn(usize)->Option<&'a usize>>(&self, args:&mut Vec<isize>, pc:usize, f:&'a F) {
        args.clear();
        for (i,a) in self.args.iter().enumerate() {
            if i < self.labels.len() {
                if let Some(index) = self.labels[i] {
                    match f(index) {
                        None    => args.push(*a),
                        Some(x) => args.push((*x) as isize - (pc as isize)),
                    }
                } else {
                    args.push(*a);
                }
            } else {
                args.push(*a);
            }
        }
    }

    //zz All done
}

//a PicoIRProgram
//pt PicoIRProgram
#[derive(Debug)]
/// The PicoIRProgram represents a program consisting of PicoIRInstructions
pub struct PicoIRProgram {
    pub code      : Vec<PicoIRInstruction>,
    labels        : LabelPool,
}

//ip PicoIRProgram
impl PicoIRProgram {
    //fp new
    /// Create a new PicoIRProgram
    pub fn new() -> Self {
        Self {
            code   : Vec::new(),
            labels : LabelPool::new(),
        }
    }

    //mp get_label_index
    pub fn get_label_index(&self, s:&str) -> Option<usize> {
        self.labels.get_label_index(s)
    }
    
    //mp add_label_at_index
    /// Add a new label with a given index
    pub fn add_label_at_index(&mut self, label:String, index:usize) {
        self.labels.add_label_at_index(label, index)
    }

    //mp add_label
    /// Add a new label with the current PC
    pub fn add_label(&mut self, label:String) {
        self.add_label_at_index(label, self.code.len())
    }

    //mp add_instruction
    /// Add an instruction at the end of the current code
    pub fn add_instruction(&mut self, inst:PicoIRInstruction) {
        self.code.push(inst);
    }

    //mp resolve
    pub fn resolve<F:Fn(PicoIRIdentType, &str) -> Option<isize>>(&mut self, f:&F) -> bool {
        let mut is_resolved = true;
        for i in &mut self.code {
            is_resolved = is_resolved & i.resolve(&self.labels, f);
        }
        is_resolved
    }

    //mp is_resolved
    /// Determine if the program is fully resolved
    pub fn is_resolved(&self) -> bool {
        for i in &self.code {
            if ! i.is_resolved() { return false; }
        }
        true
    }
    
    //mp disassemble
    pub fn disassemble(&self)  -> String {
        let mut r = String::new();
        for i in &self.code {
            r.push_str(&i.disassemble());
            r.push_str("\n");
        }
        r
    }

    //zz All done
}

//a PicoIREncoding
//pt PicoIREncoding
/// A trait that adds encoding and decoding a PicoProgram to a PicoIRProgram
pub trait PicoIREncoding : PicoProgram {
    //ti CodeFragment
    /// Type of a code fragmet
    type CodeFragment;

    //fp of_pico_ir
    /// Used to convert an instruction for a value to a vector of encodings (PicoCode)
    fn of_pico_ir(&self, inst:&PicoIRInstruction, pass:usize, args_remap:&Vec<isize>) -> Result<Self::CodeFragment, String>;

    //fp to_pico_ir
    /// Get an instruction from one or more V PicoCode words,
    /// returning instruction and number of words consumed
    fn to_pico_ir(&self, ofs:usize) -> Result<(PicoIRInstruction, usize),String>;

    //fp add_code_fragment
    /// Add a code fragment (created by of_instruction) to a PicoProgram
    fn add_code_fragment(&mut self, code_fragment:Self::CodeFragment) -> usize;
    
    //fp new_code_fragment
    /// Create a new code fragment to add other code fragments to
    fn new_code_fragment(&self) -> Self::CodeFragment;
    
    //fp append_code_fragment
    /// Append to a code fragment
    fn append_code_fragment(&self, code:&mut Self::CodeFragment, fragment:Self::CodeFragment) -> usize;
    
    //fp get_code_fragment_pc
    /// Get the PC of the end of the code fragment for branch offset determination
    fn get_code_fragment_pc(&self, code:&Self::CodeFragment) -> usize;
    
    //fp of_program
    /// A provided method to convert a PicoIRProgram into a PicoProgram
    fn of_program(&mut self, ir_program:&PicoIRProgram) -> Result<(), String> {
        let mut pc_of_index = Vec::new();
        let mut args_remap  = Vec::new();
        let mut cf = self.new_code_fragment();
        for (i,ir) in ir_program.code.iter().enumerate() {
            let code_fragment = self.of_pico_ir(ir, 0, &args_remap )?; // First pass
            pc_of_index.push( self.append_code_fragment(&mut cf, code_fragment) );
        }
        let mut loop_count = 0;
        loop {
            let mut changed : usize = 0;
            let mut cf = self.new_code_fragment();
            for (i,ir) in ir_program.code.iter().enumerate() {
                let pc = self.get_code_fragment_pc(&cf);
                ir.remap_branch_args(&mut args_remap, pc, &|x| pc_of_index.get(x));
                let code_fragment = self.of_pico_ir(ir, 1, &args_remap)?;
                let new_pc = self.append_code_fragment(&mut cf, code_fragment);
                if pc_of_index[i] != new_pc {
                    changed += 1;
                }
                pc_of_index[i] = new_pc;
            }
            println!("Changed {}",changed);
            if changed == 0 {
                self.add_code_fragment(cf);
                break;
            }
            loop_count += 1;
            if loop_count > 10 {
                panic!("Looping in program generation hit {} loops", loop_count);
            }
        }
        Ok(())
    }

    //mp disassemble_code
    fn disassemble_code(&self, start:usize, end:usize) -> Result<Vec<String>,String> {
        let mut ptr = start;
        let mut r = Vec::new();
        while ptr < end {
            let (inst, pc_inc) = self.to_pico_ir(ptr)?;
            r.push(inst.disassemble());
            ptr += pc_inc;
        }
        Ok(r)
    }

    //zz All done
}

//a Test
#[cfg(test)]
mod test {
    use crate::base::{PicoProgram};
    use crate::base::{Opcode, AccessOp};
    use super::*;
    #[test]
    fn test0 () {
        let instructions =
            vec![
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::Const  as usize), vec![1], vec![None] ),
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::Const  as usize), vec![1], vec![None] ),
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::EnvAcc as usize), vec![0], vec![Some((PicoIRIdentType::EnvAcc, "text".to_string()))] ),
                PicoIRInstruction::make( Opcode::GetField, None, vec![0], vec![Some((PicoIRIdentType::FieldName, "Diagram::TextElement.magnet".to_string()))] ),
                PicoIRInstruction::make( Opcode::Apply,    None, vec![3], vec![None] ),
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::EnvAcc as usize), vec![0], vec![Some((PicoIRIdentType::EnvAcc, "self".to_string()))] ),
                PicoIRInstruction::make( Opcode::GetField, None, vec![0], vec![Some((PicoIRIdentType::FieldName, "Diagram::PathElement.path".to_string()))] ),
                PicoIRInstruction::make( Opcode::GetField, None, vec![0], vec![Some((PicoIRIdentType::FieldName, "Geometry::BezierPath.add_point".to_string()))] ),
                PicoIRInstruction::make( Opcode::Apply,    None, vec![1], vec![None] ),
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::Const  as usize), vec![0x1000], vec![None] ),
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::EnvAcc as usize), vec![0], vec![Some((PicoIRIdentType::EnvAcc, "rng".to_string()))] ),
                PicoIRInstruction::make( Opcode::GetField, None, vec![0], vec![Some((PicoIRIdentType::FieldName, "Geometry::Range.pt".to_string()))] ),
                PicoIRInstruction::make( Opcode::Apply,    None, vec![1], vec![None] ),
                PicoIRInstruction::make( Opcode::AccessOp, Some(AccessOp::Acc as usize), vec![1], vec![None] ),
            ];
        let mut p = PicoIRProgram::new();
        for i in instructions {
            p.add_instruction(i);
        }
        
        assert_eq!(false, p.is_resolved());
        fn resolver(map:Vec<(&str,isize)>, id_type:PicoIRIdentType, id:&str) -> Option<isize> {
            println!("{:?} {}",id_type, id);
            for (k,v) in map {
                if id == k { return Some(v); }
            }
            None
        }
        
        p.resolve(&|a,b| resolver(vec![], a,b));
        assert_eq!(false, p.is_resolved());

        println!("Resolve environment");

        p.resolve(&|a,b| resolver(vec![("text",0), ("self",1), ("rng",2)], a,b));
        assert_eq!(false, p.is_resolved());

        println!("Resolve module Geometry");

        p.resolve(&|a,b| resolver(vec![("Geometry::Range.pt",16), ("Geometry::BezierPath.add_point",12)], a,b));
        assert_eq!(false, p.is_resolved());

        println!("Final resolution - Diagram");
        
        p.resolve(&|a,b| resolver(vec![("Diagram::TextElement.magnet",10), ("Diagram::PathElement.path",4)], a,b));

        assert!(p.is_resolved());
    }
}
