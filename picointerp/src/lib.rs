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

Each stack frame contains:

* last number of extra args

* PC to return to

* environmment for the current function evaluation, with a 'return
  address' and 'previous environment', and the first K values in the
  execution environment. This is a heap object with field.0 == PC of
  caller code, .1 -> .N the N arguments provided within the closure.

### env : Environment

An environment is an object describing a function execution. It
contains (when complete) concrete *pvalue*s (WHNF) for all of the
arguments for the function, and the program counter for the
execution. How complete the environment is is described by
`extra_args`; if this is 0, then it is complete, but if it is >=1 then
that number of more arguments are required to be resolved to WHNF for
execution of the environment.

One environment is the current environment for the current function
evaluation. The first N arguments to the current function evaluation
are in the environment object; the rest are on the stack.

The *Grab* (N) instruction is the mechanism used at the start of a Curried function to either:

a.  Create a closure of size N+1 with the top ? stack words; return this

b. To pop the environment on to the stack, if the environment is
*full*, and therefore run the execution of the function (i.e. at this
point the function is Uncurried

An environment is created in picocode using the Closure(M,N)
    instruction, which allocates a closure object on the heap of size
    M, filling it with PC+N as the address to execute and with M
    arguments taken from the stack. For a partial application the
    environment may be partial.

### extra_args *usize*

This is the number of extra arguments supplied by the caller of a closure on the stack.

When a closure is applied it consists of a PC, an environment that it
should be execued within, and N *pvalue*s, and the caller provides K
more on the stack. The value of K is put in 'extra_args', and the
environment is set to the closure, and the PC set to that of the
closure.

A function 'F' of two arguments that requires both for continued
execution will have a closure created for it with the enclosing environment, N=0 and PC of F. The
function will be *preceded* by a RESTART instruction, and then its
first instruction will be GRAB(1), to indicate that it requires two
arguments - every closure invocation has one argument as a
minimum.

When this closure is invoked with an apply of 1 - i.e. with just one
*argument and hence extra_args is 0, the PC and environment will have
*been taken from the closure. The GRAB(1) instruction will create a
*new closure with the one provided argument, the environment, and a PC
*of the preceding* RESTART instruction, and returns using the top
*stack frame (return PC, enviroment, extra_args).

When this second closure is invoked with extra_args of 0 (indicating 1
argument) the RESTART instruction will look at the closure, see it has
1 argument in it (size of closure minus PC and environment), and it
will push these arguments on to the stack - in this case adding the 1
argument from the closure to that already provided; it then adds this
to extra_args (making it 1), and the code continues with the Grab(1).

If the function code is reached with extra_args of 1, then the Grab(1)
will continue execution of the function - as its arguments are ready -
but it will decrease extra_args by the 1 that was grabbed.

When the function end point is reached, it may execute a RETURN
instruction. For this function invocation extra_args is zero, and so a
simple return to the caller is performed by popping the stack frame -
the result of the call is in the accumulator.

If, though, the function had been invoked with two extra_args
(indicating an invocation of F with three arguments) then the GRAB(1)
will leave extra_args with 1, and the RETURN assumes the accumulator
is an environment and invokes that but with extra_args reduced by one to
zero. (why?)

Together `env` and `extra_args` form the closure cache described in
3.4 of Leroy's dissertation; `env` is the persistent environment,
`extra_args` is the size of the volatile

### PC *usize*

This is the offset or address in the picocode vector of the current instruction

### Initial state

Initially the state is set to:

* Stack = Vec::new(), and hence SP=0

* PC = program address

* extra_args = 0 - no more arguments are required to execute this function

* env = Unit - there is no previous environment

* accumulator = *pvalue* of integer 0

## Picocode Instructions

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

* MakeBlock(tag,N) 

    Allocates a new block on the heap, with the given tag; it will have N>0 fields, and the *first* field is set to the value of the accumulator.

    The accumulator is then set to the heap object

* GetField(N) 

    Accumulator is an object; read its Nth field, and set the accumulator to that

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
   done that need to be popped before the original arguments and call
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

// Object-oriented operations 

#define Lookup(obj, lab) Field (Field (obj, 0), Int_val(lab))

    Instruct(GETMETHOD):
      accu = Lookup(sp[0], accu);
      Next;

    Instruct(GETPUBMET):
      *--sp = accu;
      accu = Val_int(*pc);
      pc += 2;
//    Fallthrough 
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
mod pico_ir;
mod interpreter;
// mod assemble;
mod isize_int;

//a Exports
pub use types::{PicoValue, PicoCode, PicoHeap, PicoProgram};
use interpreter::PicoInterp;
pub type PicoProgramIsize = isize_int::IsizeProgram;
pub type PicoInterpIsize<'a> = PicoInterp<'a, isize, isize, Vec<isize>>;
