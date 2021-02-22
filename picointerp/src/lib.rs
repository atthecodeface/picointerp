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

The picointerpreter architecture is heavily based on the Zinc Abstract
Machine by Xavier Leroy, used in Ocaml. It's purpose there was to
provide a machine that would efficiently handle curried functions
without requiring creation of many closure objects.

## Picointerpreter architecture

The picointerpreter has internal state of:

### Accumulator : *pvalue*

The accumulator is used for calculations to stop every operatioon
requiring manipulation of the stack.

### Stack - a pile of *pvalue*

For picointerpreter the stack is an *upward* growing stack (a pile?) of *pvalue*s.

The stack holds stack frames. Each stack pushed frame - consists of a
header of three words, the *extra_args*, *env* and *pc*.

With the stack frames, each function execution in progress on the
stack has its own enviroment; the stack is both an argument stack and
an environmet stack.

### Environment

An environment is an object describing the invoking closure, whose contents are
the PC of the code of the function and the *pvalue*s of the arguments for the closure.

An environment is created in picocode using the Closure(M,N)
    instruction, which allocates a closure object on the heap of size
    M, filling it with PC+N as the address to execute and with M
    arguments taken from the stack. For a partial application the
    environment may be partial

* extra_args : *usize* - if >0 this is the number of extra arguments
   required to complete the current environment for the code to be able
   to execute.

* PC : *usize* - offset ('address') in the picocode vector of the current instruction

* SP : *usize* - where the next element will be added to the stack (i.e. stack.len() in Rust terms)

Initially the state is set to:

* Stack = Vec::new(), and hence SP=0

* PC = program address

* extra_args = 0

* env = Unit

* accumulator = *pvalue* of integer 0

The stack contains the stack frame. This should be:

* last number of extra args

* PC to return to

* environmment for invocation of the closure on the heap (this is
  always a Closure object I beleive); this object has .0 == PC of
  code, .1 -> .N the N arguments provided within the closure.

### Stack and constant instructions

* Const : Accumulator = integer [0-3]

* Acc: Accumulator = stack[0-7]

* PushConst : Push accumulator, accumulator = integer [0-3]

* PushAcc(N): Push accumulataor, accumulator=stack[N] (Push is identical to PushAcc[0])

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

   returns from a function where X local stack allocations had been
   done that need to be popped before the originall arguments and call
   stack had been added.

* Closure(0,N): accumulator = Alloc(closure,1), accumulator.as_env(0)=PC+N

   Why does this not push the accumulator?

* Closure(M,N): stack.push(accumulator), accumulator = Alloc(closure,1+M), accumulator.as_env([0..M+1]) = (PC, stack.pop(M))


To compile ocaml to its bytecode:


```text
ocaml -dinstr test.ml

module Shm = struct
type t_point = {
  x:int;
  y:int;
}
let create x y : t_point = { x; y }
let midpoint p0 p1 = 
let x = (p0.x + p1.x) / 2 in
let y = (p0.y + p1.y) / 2 in
{ x; y}

end

        const 0a
        return 1

        const 0a
        return 1

        closure L2, 0 ; fn create x y
        push
        closure L1, 0 ; fn midpoint p0 p1
        push
        event "./test.ml" 711-883
        acc 0
        push
; Stack is closure(create); closure(midpoint)closure(create); closure(midpoint); closure(midpoint)
        acc 2
; accumulator = Make a record of closure(create); closure(midpoint), and pop last of stack
        makeblock 2, 0
; Stack is closure(create); closure(midpoint)
        pop 2
; Stack is empty
        push
; Stack is Record { closure(create); closure(midpoint); }
        const "Shm/1009"
        push
; Stack is Record { closure(create); closure(midpoint); } Shm/1009
        getglobal Toploop!
        getfield 1
        appterm 2, 3
        restart

let midpoint p0 p1 = 
let x = (p0.x + p1.x) / 2 in
let y = (p0.y + p1.y) / 2 in
{ x; y}


 ; This is midpoint p0 p1
 ; First we 'grab 1' as we reqire *two* arguments not *one*
L1:     grab 1
 ; Now extra_args should be 1
 ; env -> ?
 ; The stack should be [ ret_pc ; last_env ; last_extra_args ] p1 p0
 ; p0 and p1 are records on the heap - objects of type 0 with 2 entries
 ;
 ; The event just shows where in the source it is - these should be removed
        event "./test.ml" 813-878
        const 2
        push
        acc 2
 ; Stack is ... p1 p0 2; accumulator = p1
        getfield 0
        push
        acc 2
 ; Stack is ... p1 p0 2 p1.x; accumulator = p0
        getfield 0
 ; Stack is ... p1 p0 2 p1.x; accumulator = p0.x
        addint
        divint
 ; Stack is ... p1 p0 ; accumulator = (p1.x+p0.x)/2
        push
        event "./test.ml" 842-878
 ; Stack is ... p1 p0 (p1.x+p0.x)/2
        const 2
        push
        acc 3
        getfield 1
        push
        acc 3
        getfield 1
        addint
        divint
        push
 ; Stack is ... p1 p0 (p1.x+p0.x)/2 (p1.y+p0.y)/2
        event "./test.ml" 871-878
        acc 0
        push
        acc 2
 ; Stack is ... p1 p0 (p1.x+p0.x)/2 (p1.y+p0.y)/2 (p1.y+p0.y)/2; accumulator = (p1.x+p0.x)/2
 ; Make a new record of 2 elements with the midpoints - pops one
        makeblock 2, 0
        return 4
        restart

 ; This is fn create x y
 ; First we 'grab 1', as create requires *two* arguments
L2:     grab 1
 ; Now extra_args should be 1
 ; env -> ?
 ; The stack should be [ ret_pc ; env ; extra_args ] y x
 ;
 ; The event just shows where in the source it is - these should be removed
        event "./test.ml" 782-790
 ; - get y from the stack and push it
        acc 1
        push
 ; - get x from the stack in to accumulator
        acc 1
 ; The stack should be [ ret_pc ; last_env ; last_extra_args ] y x y, acc=x
        makeblock 2, 0
 ; Make a block (on the heap) of type 0 with 2 elements - this is a 'record'
 ; This pops *1* (y) - and last element of record is y
 ; The stack should be [ ret_pc ; last_env ; last_extra_args ] y x
 ; Now pop 2 and return
        return 2
 ; pc = ret_pc ; env = last_env; extra_args = last_extra_args

        const 0a
        return 1
```

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
#[macro_use]
extern crate num_derive;
extern crate num;
extern crate regex;
#[macro_use]
extern crate lazy_static;

mod types;
mod interpreter;
mod assemble;
mod isize_int;

//a Exports
pub use types::{PicoValue, PicoCode, PicoHeap};
use interpreter::PicoInterp;
pub type PicoInterpIsize<'a> = PicoInterp<'a, isize, Vec<isize>>;
