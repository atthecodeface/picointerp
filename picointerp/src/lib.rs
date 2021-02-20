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

@file    lib.rs
@brief   Picointerpreter library
 */

//a Documentation
// #![warn(missing_docs)]
// #![warn(missing_doc_code_examples)]
/*!
# Picointerpreter library

The picointerpreter runs in a very similar fashion to the Ocaml
'byte-code' interpreter, in that it has a stack and heap with every
element in the stack being an integer or an object reference. We
denote this type as *pvalue*. The code that the interpreter runs is
*picocode*.

For really small applications the heap is required only for closures - the only
operations permitted with this interpreter are boolean and integer
operations, and function invocations.

Each object is identified in its reference with the bottom bit clear,
integers with the bottom bit set ; an object reference is an index in
to the heap, which is a vec of isize elements; an object reference
cannot be zero, as a value of 0 represents Unit or () in Rust terms.

The heap contains objects which have a first word that its a tag. The
tag has a 24-bit size-of-object, and an 8-bit object type.

Picocode instructions may be one or two elements long: the former are
known as *immediate* operations, the others *value* operations. In the
instruction reference below an instruction of the form Blah(N) are
value operations, where N is held in the second element of the code.

The picointerpreter architecture is copied from Ocaml.

## Picointerpreter architecture

The picointerpreter has internal state of:

* Accumulator : *pvalue*

* Stack - an *upward* growing stack (a pile?) of *pvalue*

* Environment - an object of the invoking closure, whose contents are
    *(if environment is not Unit) PC of the code of the function and
    *the pvalue*s of the arguments for the closure. This is created in
    *picocode using the Closure(M,N) instruction, which allocates a
    *closure object on the heap of size M, filling it with PC+N as the
    *address to execute and with M arguments taken from the stack

* extra_args : *usize* - if >0 this is the number of 

* PC : *usize* - offset ('address') in the picocode vector of the current instruction

* SP : *usize* - where the next element will be added to the stack (i.e. stack.len() in Rust terms)

Initially the state is set to:

* Stack = Vec::new(), and hence SP=0

* PC = program address

* extra_args = 0

* env = Unit

* accumulator = *pvalue* of integer 0

### Stack and constant instructions

* ConstN : Accumulator = integer [0-3]

* Const(N) : Accumulator = integer N

* AccN: Accumulator = stack[0-7]

* Acc(N): Accumulator=stack[N]

* PushConstN : Push accumulator, accumulator = integer [0-3]

* PushConst(N) : Push accumulator, accumulator = integer N

* PushAccN: Push accumulator, accumulator=stack[0-7]

* PushAcc(N): Push accumulataor, accumulator=stack[N]

* Pop(N) : SP += N

* Assign(N): stack[N] = accumulator, accumulator = Unit

### Integer arithmetic

* IntNegate: accumulator = -accumulator

* IntAdd/Sub: accumulator = accumulator + - stack.pop()

* IntMul/Div/Mod: accumulator = accumulator * / % stack.pop()

* IntAnd/Or/Xor: accumulator = accumulator & | ^ % stack.pop()

* IntLsl/Lsr/Asr: accumulator = accumulator << >> >>> stack.pop()

### Integer comparison and branch

* IntCmpCC : accumulator = accumulator CMP stack.pop()

* IntBCC(N) : if accumulator == stack.pop() { PC += N }

where CC is:

* EQ => ==

* NE => !=

* LT => <

* LE => <=

* GT => <

* GE => >=

* ULT => <= unsigned

* UGE => >= unsigned

### Miscellaneous integer

* OffsetInt(N) : accumulator += N

* IsInt(N) : accumulator = { if accumulator is integer {1} else {0} }

### Object handling

* OffsetRef(N) : Field(accumulator, 0) += N; accumulator = Unit

### Closure access

* EnvAccN: N=1-4; Accumulator = Field(env, N)

* EnvAcc(N): Accumulator = Field(env, N)

* PushEnvAccN: N=1-4; Push accumulator, accumulator = Field(env, N)

* PushEnvAcc(N): Push accumulator, accumulator = Field(env, N)

### Function handling - invoke a closure and return from closure

* Apply(N) : extra_args=N-1, PC=accumulator.as_env(0), env=accumulator

* ApplyN : N=1-4; extra_args=N-1, PC=accumulator.as_env(0), env=accumulator, stack.push( extra_args, env, PC, stack[0..N-1])

* AppTermN(X): N=1-4; Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)

* AppTerm(N, X): Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)

* PushRetAddr(N) : stack.push( extra_args, env, PC+N )

* Return(X): stack.adjust(-X); if extra_args>0 {Apply(extra_args)} else { pc,env,extra_args=stack.pop(3); }

* Closure(0,N): accumulator = Alloc(closure,1), accumulator.as_env(0)=PC+N

   Why does this not push the accumulator?

* Closure(M,N): stack.push(accumulator), accumulator = Alloc(closure,1+M), accumulator.as_env([0..M+1]) = (PC, stack.pop(M))

```text
    Instruct(RESTART): {
      int num_args = Wosize_val(env) - 2;
      int i;
      sp -= num_args;
      for (i = 0; i < num_args; i++) sp[i] = Field(env, i + 2);
      env = Field(env, 1);
      extra_args += num_args;
      Next;
    }

    Instruct(GRAB): {
      int required = *pc++;
      if (extra_args >= required) {
        extra_args -= required;
      } else {
        mlsize_t num_args, i;
        num_args = 1 + extra_args; // arg1 + extra args 
        Alloc_small(accu, num_args + 2, Closure_tag);
        Field(accu, 1) = env;
        for (i = 0; i < num_args; i++) Field(accu, i + 2) = sp[i];
        Code_val(accu) = pc - 3; // Point to the preceding RESTART instr.
        sp += num_args;
        pc = (code_t)(sp[0]);
        env = sp[1];
        extra_args = Long_val(sp[2]);
        sp += 3;
      }
      Next;
    }

    Instruct(CLOSUREREC): {
      int nfuncs = *pc++;
      int nvars = *pc++;
      int i;
      value * p;
      if (nvars > 0) *--sp = accu;
      Alloc_small(accu, nfuncs * 2 - 1 + nvars, Closure_tag);
      p = &Field(accu, nfuncs * 2 - 1);
      for (i = 0; i < nvars; i++) {
        *p++ = sp[i];
      }
      sp += nvars;
      p = &Field(accu, 0);
      *p = (value) (pc + pc[0]);
      *--sp = accu;
      p++;
      for (i = 1; i < nfuncs; i++) {
        *p = Make_header(i * 2, Infix_tag, Caml_white);  // color irrelevant.
        p++;
        *p = (value) (pc + pc[i]);
        *--sp = (value) p;
        p++;
      }
      pc += nfuncs;
      Next;
    }

    Instruct(PUSHOFFSETCLOSURE):
      *--sp = accu; // fallthrough
    Instruct(OFFSETCLOSURE):
      accu = env + *pc++ * sizeof(value); Next;

    Instruct(PUSHOFFSETCLOSUREM2):
      *--sp = accu; // fallthrough
    Instruct(OFFSETCLOSUREM2):
      accu = env - 2 * sizeof(value); Next;
    Instruct(PUSHOFFSETCLOSURE0):
      *--sp = accu; // fallthrough
    Instruct(OFFSETCLOSURE0):
      accu = env; Next;
    Instruct(PUSHOFFSETCLOSURE2):
      *--sp = accu; // fallthrough
    Instruct(OFFSETCLOSURE2):
      accu = env + 2 * sizeof(value); Next;




// Function application

// Access to global variables

    Instruct(PUSHGETGLOBAL):
      *--sp = accu;
      // Fallthrough
    Instruct(GETGLOBAL):
      accu = Field(caml_global_data, *pc);
      pc++;
      Next;

    Instruct(PUSHGETGLOBALFIELD):
      *--sp = accu;
      // Fallthrough
    Instruct(GETGLOBALFIELD): {
      accu = Field(caml_global_data, *pc);
      pc++;
      accu = Field(accu, *pc);
      pc++;
      Next;
    }

    Instruct(SETGLOBAL):
      caml_modify(&Field(caml_global_data, *pc), accu);
      accu = Val_unit;
      pc++;
      Next;

// Allocation of blocks

    Instruct(PUSHATOM0):
      *--sp = accu;
      // Fallthrough
    Instruct(ATOM0):
      accu = Atom(0); Next;

    Instruct(PUSHATOM):
      *--sp = accu;
      // Fallthrough
    Instruct(ATOM):
      accu = Atom(*pc++); Next;

    Instruct(MAKEBLOCK): {
      mlsize_t wosize = *pc++;
      tag_t tag = *pc++;
      mlsize_t i;
      value block;
      if (wosize <= Max_young_wosize) {
        Alloc_small(block, wosize, tag);
        Field(block, 0) = accu;
        for (i = 1; i < wosize; i++) Field(block, i) = *sp++;
      } else {
        block = caml_alloc_shr(wosize, tag);
        caml_initialize(&Field(block, 0), accu);
        for (i = 1; i < wosize; i++) caml_initialize(&Field(block, i), *sp++);
      }
      accu = block;
      Next;
    }
    Instruct(MAKEBLOCK1): {
      tag_t tag = *pc++;
      value block;
      Alloc_small(block, 1, tag);
      Field(block, 0) = accu;
      accu = block;
      Next;
    }
    Instruct(MAKEBLOCK2): {
      tag_t tag = *pc++;
      value block;
      Alloc_small(block, 2, tag);
      Field(block, 0) = accu;
      Field(block, 1) = sp[0];
      sp += 1;
      accu = block;
      Next;
    }
    Instruct(MAKEBLOCK3): {
      tag_t tag = *pc++;
      value block;
      Alloc_small(block, 3, tag);
      Field(block, 0) = accu;
      Field(block, 1) = sp[0];
      Field(block, 2) = sp[1];
      sp += 2;
      accu = block;
      Next;
    }
    Instruct(MAKEFLOATBLOCK): {
      mlsize_t size = *pc++;
      mlsize_t i;
      value block;
      if (size <= Max_young_wosize / Double_wosize) {
        Alloc_small(block, size * Double_wosize, Double_array_tag);
      } else {
        block = caml_alloc_shr(size * Double_wosize, Double_array_tag);
      }
      Store_double_field(block, 0, Double_val(accu));
      for (i = 1; i < size; i++){
        Store_double_field(block, i, Double_val(*sp));
        ++ sp;
      }
      accu = block;
      Next;
    }

// Access to components of blocks

    Instruct(GETFIELD0):
      accu = Field(accu, 0); Next;
    Instruct(GETFIELD1):
      accu = Field(accu, 1); Next;
    Instruct(GETFIELD2):
      accu = Field(accu, 2); Next;
    Instruct(GETFIELD3):
      accu = Field(accu, 3); Next;
    Instruct(GETFIELD):
      accu = Field(accu, *pc); pc++; Next;
    Instruct(GETFLOATFIELD): {
      double d = Double_field(accu, *pc);
      Alloc_small(accu, Double_wosize, Double_tag);
      Store_double_val(accu, d);
      pc++;
      Next;
    }

    Instruct(SETFIELD0):
      modify_dest = &Field(accu, 0);
      modify_newval = *sp++;
    modify:
      Modify(modify_dest, modify_newval);
      accu = Val_unit;
      Next;
    Instruct(SETFIELD1):
      modify_dest = &Field(accu, 1);
      modify_newval = *sp++;
      goto modify;
    Instruct(SETFIELD2):
      modify_dest = &Field(accu, 2);
      modify_newval = *sp++;
      goto modify;
    Instruct(SETFIELD3):
      modify_dest = &Field(accu, 3);
      modify_newval = *sp++;
      goto modify;
    Instruct(SETFIELD):
      modify_dest = &Field(accu, *pc);
      pc++;
      modify_newval = *sp++;
      goto modify;
    Instruct(SETFLOATFIELD):
      Store_double_field(accu, *pc, Double_val(*sp));
      accu = Val_unit;
      sp++;
      pc++;
      Next;

// Array operations

    Instruct(VECTLENGTH): {
      mlsize_t size = Wosize_val(accu);
      if (Tag_val(accu) == Double_array_tag) size = size / Double_wosize;
      accu = Val_long(size);
      Next;
    }
    Instruct(GETVECTITEM):
      accu = Field(accu, Long_val(sp[0]));
      sp += 1;
      Next;
    Instruct(SETVECTITEM):
      modify_dest = &Field(accu, Long_val(sp[0]));
      modify_newval = sp[1];
      sp += 2;
      goto modify;

// String operations 

    Instruct(GETSTRINGCHAR):
      accu = Val_int(Byte_u(accu, Long_val(sp[0])));
      sp += 1;
      Next;
    Instruct(SETSTRINGCHAR):
      Byte_u(accu, Long_val(sp[0])) = Int_val(sp[1]);
      sp += 2;
      accu = Val_unit;
      Next;

// Branches and conditional branches 

    Instruct(BRANCH):
      pc += *pc;
      Next;
    Instruct(BRANCHIF):
      if (accu != Val_false) pc += *pc; else pc++;
      Next;
    Instruct(BRANCHIFNOT):
      if (accu == Val_false) pc += *pc; else pc++;
      Next;
    Instruct(SWITCH): {
      uint32 sizes = *pc++;
      if (Is_block(accu)) {
        intnat index = Tag_val(accu);
        Assert ((uintnat) index < (sizes >> 16));
        pc += pc[(sizes & 0xFFFF) + index];
      } else {
        intnat index = Long_val(accu);
        Assert ((uintnat) index < (sizes & 0xFFFF)) ;
        pc += pc[index];
      }
      Next;
    }
    Instruct(BOOLNOT):
      accu = Val_not(accu);
      Next;

// Object-oriented operations 

#define Lookup(obj, lab) Field (Field (obj, 0), Int_val(lab))

//    / please don't forget to keep below code in sync with the
//         functions caml_cache_public_method and
//         caml_cache_public_method2 in obj.c 

    Instruct(GETMETHOD):
      accu = Lookup(sp[0], accu);
      Next;

#define CAML_METHOD_CACHE
#ifdef CAML_METHOD_CACHE
    Instruct(GETPUBMET): {
//     accu == object, pc[0] == tag, pc[1] == cache 
      value meths = Field (accu, 0);
      value ofs;
#ifdef CAML_TEST_CACHE
      static int calls = 0, hits = 0;
      if (calls >= 10000000) {
        fprintf(stderr, "cache hit = %d%%\n", hits / 100000);
        calls = 0; hits = 0;
      }
      calls++;
#endif
      *--sp = accu;
      accu = Val_int(*pc++);
      ofs = *pc & Field(meths,1);
      if (*(value*)(((char*)&Field(meths,3)) + ofs) == accu) {
#ifdef CAML_TEST_CACHE
        hits++;
#endif
        accu = *(value*)(((char*)&Field(meths,2)) + ofs);
      }
      else
      {
        int li = 3, hi = Field(meths,0), mi;
        while (li < hi) {
          mi = ((li+hi) >> 1) | 1;
          if (accu < Field(meths,mi)) hi = mi-2;
          else li = mi;
        }
        *pc = (li-3)*sizeof(value);
        accu = Field (meths, li-1);
      }
      pc++;
      Next;
    }
#else
    Instruct(GETPUBMET):
      *--sp = accu;
      accu = Val_int(*pc);
      pc += 2;
//    Fallthrough 
#endif
    Instruct(GETDYNMET): {
//    accu == tag, sp[0] == object, *pc == cache 
      value meths = Field (sp[0], 0);
      int li = 3, hi = Field(meths,0), mi;
      while (li < hi) {
        mi = ((li+hi) >> 1) | 1;
        if (accu < Field(meths,mi)) hi = mi-2;
        else li = mi;
      }
      accu = Field (meths, li-1);
      Next;
    }
```

!*/

//a Imports

//a Global constants for debug
// const DEBUG_MAIN      : bool = 1 == 0;

//a Main
//pc Const
const INT_OP_NEG : usize    = 0;
const INT_OP_ADD : usize    = 1;
const INT_OP_SUB : usize    = 2;
const INT_OP_MUL : usize    = 3;
const INT_OP_DIV : usize    = 4;
const INT_OP_MOD : usize    = 5;
const INT_OP_AND : usize    = 6;
const INT_OP_OR  : usize    = 7;
const INT_OP_XOR : usize    = 8;
const INT_OP_LSL : usize    = 9;
const INT_OP_LSR : usize    = 10;
const INT_OP_ASR : usize    = 11;

//pt PicoInstructionOpcode
pub enum PicoInstructionOpcode {
    Const     = 0x00, // imm of 0-3 or integer value
    Acc       = 0x01, // imm of 0-7 or integer value
    PushConst = 0x02, // imm of 0-3 or integer value
    PushAcc   = 0x03, // N = offset in to stack
    Pop       = 0x04, // N = usize to adjust stack by
    Assign    = 0x05, // N = offset in to stack
    IntOp     = 0x06, // N => negate, ?, add, sub, mul, div, mod, ?, and, or, xor, ?, lsl, lsr, asr, ?
    IntCmp    = 0x07, // N => eq, ne, lt, le, gt, ge, ult, uge,
    IntBranch = 0x08, // N => eq, ne, lt, le, gt, ge, ult, uge,
    /*
* OffsetInt(N) : accumulator += N
* IsInt(N) : accumulator = { if accumulator is integer {1} else {0} }
* OffsetRef(N) : Field(accumulator, 0) += N; accumulator = Unit
* EnvAccN: N=1-4; Accumulator = Field(env, N)
* EnvAcc(N): Accumulator = Field(env, N)
* PushEnvAccN: N=1-4; Push accumulator, accumulator = Field(env, N)
* PushEnvAcc(N): Push accumulator, accumulator = Field(env, N)
* Apply(N) : extra_args=N-1, PC=accumulator.as_env(0), env=accumulator
* ApplyN : N=1-4; extra_args=N-1, PC=accumulator.as_env(0), env=accumulator, stack.push( extra_args, env, PC, stack[0..N-1])
* AppTermN(X): N=1-4; Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)
* AppTerm(N, X): Data = stack[0..N]; stack.adjust(-X); stack.push(Data[0..N]); Apply(extra_args+1)
* PushRetAddr(N) : stack.push( extra_args, env, PC+N )
* Return(X): stack.adjust(-X); if extra_args>0 {Apply(extra_args)} else { pc,env,extra_args=stack.pop(3); }
* Closure(0,N): accumulator = Alloc(closure,1), accumulator.as_env(0)=PC+N
* Closure(M,N): stack.push(accumulator), accumulator = Alloc(closure,1+M), accumulator.as_env([0..M+1]) = (PC, stack.pop(M))
*/
}

//pt PicoCode
/// A picocode value, with mechanisms to break it in to opcode,
/// immediate value, and to get integer values from it as isize or
/// usize
pub trait PicoCode<V:PicoValue> : Clone + Copy + Sized {
    fn opcode_class(self) -> PicoInstructionOpcode;
    fn opcode_n(self)     -> usize;
    fn is_imm(self) -> bool;
    fn imm_value(self) -> V;
    fn imm_usize(self) -> usize;
    fn as_value(self) -> V;
    fn as_usize(self) -> usize;
}

//pt PicoHeap
/// An implementation of a heap
/// Heap objects
pub trait PicoHeap : Sized {
    fn new() -> Self;
    fn alloc(n:usize) -> usize; // allocations *must* be even numbers
}

//pt PicoValue
/// The value used by the interpreter this is notionally forced to be an integer of some size whose bottom bit is 0 for an object (with the value being usable as an index)
pub trait PicoValue : Sized + Clone + Copy + std::fmt::Debug {
    /* const */ fn unit() -> Self;
    /* const */ fn int(n:isize) -> Self;
    /* const */ fn is_int(self) -> bool;
    /* const */ fn is_object(self) -> bool { ! self.is_int() }
    /* const */ fn as_isize(self) -> isize;
    /* const */ fn as_usize(self) -> usize;
    /* const */ fn as_heap_index(self) -> usize; // Guaranteed to be invoked only if is_object
    fn negate(self) -> Self;
    fn add(self, other:Self) -> Self;
    fn sub(self, other:Self) -> Self;
    fn mul(self, other:Self) -> Self;
    fn div(self, other:Self) -> Self;
    fn rem(self, other:Self) -> Self;
    fn and(self, other:Self) -> Self;
    fn or(self, other:Self) -> Self;
    fn xor(self, other:Self) -> Self;
    fn lsl(self, other:Self) -> Self;
    fn lsr(self, other:Self) -> Self;
    fn asr(self, other:Self) -> Self;
}

//ip PicoValue for isize
impl PicoValue for isize {
    #[inline]
    /* const */ fn unit() -> Self { 0 }
    #[inline]
    /* const */ fn int(n:isize) -> Self { (n<<1) | 1 }
    #[inline]
    /* const */ fn is_int(self) -> bool { self & 1 == 1 }
    #[inline]
    /* const */ fn is_object(self) -> bool { self & 1 == 0 }
    #[inline]
    /* const */ fn as_isize(self) -> isize { self >> 1 }
    #[inline]
    /* const */ fn as_usize(self) -> usize { (self >> 1) as usize }
    #[inline]
    /* const */ fn as_heap_index(self) -> usize { self as usize }
    #[inline]
    fn negate(self) -> Self          { (! self) ^ 1 }
    fn add(self, other:Self) -> Self { self + (other-1) }
    fn sub(self, other:Self) -> Self { self - (other-1) }
    fn mul(self, other:Self) -> Self { (self>>1) * (other>>1) + 1 }
    fn div(self, other:Self) -> Self { (self>>1) / (other>>1) }
    fn rem(self, other:Self) -> Self { (self>>1) % (other>>1) }
    fn and(self, other:Self) -> Self { self & other }
    fn or(self, other:Self) -> Self  { self | other }
    fn xor(self, other:Self) -> Self { (self ^ other) + 1 }
    fn lsl(self, other:Self) -> Self { ((self-1) << (other>>1)) + 1 }
    fn lsr(self, other:Self) -> Self { (((self-1) as usize) >> (other>>1)) as isize + 1 }
    fn asr(self, other:Self) -> Self { ((self-1) >> (other>>1)) + 1 }
}

//tp PicoInterp
/// A picointerpreter with a reference to the code it has, which then
/// contains its heap and values
pub struct PicoInterp<'a, H:PicoHeap, V:PicoValue, P:PicoCode<V>> {
    code : &'a Vec<P>,
    heap : H,
    stack : Vec<V>,
    pc : usize,
    extra_args : usize,
    env  : V,
    accumulator : V,
}

//ip PicoInterp
impl <'a, H:PicoHeap, V:PicoValue, P:PicoCode<V>> PicoInterp<'a, H, V, P> {

    //fp new
    /// Create a new picointerpreter for a piece of code
    pub fn new(code : &'a Vec<P>) -> Self {
        let heap = H::new();
        let stack = Vec::new();
        let env = V::unit();
        let accumulator = V::int(0);
        Self { code, heap, stack, pc:0, extra_args:0, env, accumulator }
    }

    //mi execute
    #[inline]
    fn execute(&mut self) {
        let pc = self.pc;
        let instruction  = self.code[pc]; // PicoCode
        match instruction.opcode_class() {
            PicoInstructionOpcode::Const => {
                self.do_const(instruction);
            }
            PicoInstructionOpcode::PushConst => {
                self.stack.push(self.accumulator);
                self.do_const(instruction);
            }
            PicoInstructionOpcode::Acc => {
                self.do_acc(instruction);
            }
            PicoInstructionOpcode::PushAcc => {
                self.stack.push(self.accumulator);
                self.do_acc(instruction);
            }
            PicoInstructionOpcode::Pop => {
                let data = self.code[pc+1];
                let ofs = data.as_usize();
                let sp = self.stack.len() - ofs;
                self.stack.truncate(sp);
                self.pc += 2;
            }
            PicoInstructionOpcode::Assign => {
                let data = self.code[pc+1];
                let ofs = data.as_usize();
                let sp = self.stack.len();
                self.stack[sp-1-ofs] = self.accumulator;
                self.accumulator = V::unit();
                self.pc += 2;
            }
            PicoInstructionOpcode::IntOp => {
                self.do_int_op(instruction.imm_usize() & 0xf);
            }
            _ => {
                self.pc += 1;
            }
        }
/*
    IntCmp    : 0x07, // N => eq, ne, lt, le, gt, ge, ult, uge,
    IntBranch : 0x08, // N => eq, ne, lt, le, gt, ge, ult, uge,
         */
    }

    //mi do_const
    #[inline]
    fn do_const(&mut self, instruction:P) {
        if instruction.is_imm() {
            self.accumulator = instruction.imm_value();
            self.pc += 1;
        } else {
            let data = self.code[self.pc+1];
            self.accumulator = data.as_value();
            self.pc += 2;
        }
    }
    
    //mi do_acc
    #[inline]
    fn do_acc(&mut self, instruction:P) {
        if instruction.is_imm() {
            let ofs = instruction.imm_usize();
            let sp = self.stack.len();
            self.accumulator = self.stack[sp -1 - ofs];
            self.pc += 1;
        } else {
            let data = self.code[self.pc+1];
            let ofs = data.as_usize();
            let sp = self.stack.len();
            self.accumulator = self.stack[sp -1 - ofs];
            self.pc += 2;
        }
    }

    //mi do_int_op
    #[inline]
    fn do_int_op(&mut self, int_op:usize) {
        match int_op {
            INT_OP_NEG => { self.accumulator = self.accumulator.negate(); },
            INT_OP_ADD => { self.accumulator = self.accumulator.add(self.stack.pop().unwrap()); },
            INT_OP_SUB => { self.accumulator = self.accumulator.sub(self.stack.pop().unwrap()); },
            INT_OP_MUL => { self.accumulator = self.accumulator.mul(self.stack.pop().unwrap()); },
            INT_OP_DIV => { self.accumulator = self.accumulator.div(self.stack.pop().unwrap()); },
            INT_OP_MOD => { self.accumulator = self.accumulator.rem(self.stack.pop().unwrap()); },
            INT_OP_AND => { self.accumulator = self.accumulator.and(self.stack.pop().unwrap()); },
            INT_OP_OR  => { self.accumulator = self.accumulator.or (self.stack.pop().unwrap()); },
            INT_OP_XOR => { self.accumulator = self.accumulator.xor(self.stack.pop().unwrap()); },
            INT_OP_LSL => { self.accumulator = self.accumulator.asr(self.stack.pop().unwrap()); },
            INT_OP_LSR => { self.accumulator = self.accumulator.lsr(self.stack.pop().unwrap()); },
            INT_OP_ASR => { self.accumulator = self.accumulator.asr(self.stack.pop().unwrap()); },
            _ => { self.accumulator = self.accumulator.negate(); },
        }
    }
    
    //zz All done
}

