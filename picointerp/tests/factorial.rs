extern crate picointerp;
use picointerp::*;

mod common;

#[test]
fn blah() {
    //   this is called with 2 arguments
    //   It has 0 vars and 1 function so creates a closure of (factorial, {arg}*0, {Infix, pc}*(1-1)) which it pushes
    //   It also leaves this in the accumulator
    //   It has 1 function so it creates no more infix objects (subobjects of the closure) - these would be pushed
    //      let rec factorial acc n = if n<1 then acc else factorial (acc*n) (n-1)
        let factorial = "

; The closure we invoke with must have the env and PC be that of factorial; the stack has our return address
clos 0, factorial
appn 2
#loop br loop

; Restart as factorial does a grab
rstrt
#factorial
; At this point we could have [n] or [n acc] or [.... n acc] on the stack
     grab 1
; We have [n acc] on the top of the stack - and our environment must be {#factorial, {arg}*0}
   acc 1      pcnst 1
; Now [n acc n] on the stack, acc=1
  bcmple factorial_do
; Now [n acc] on the stack
   acc 0
; Now [n acc] on the stack, acc=acc
   ret 2
#factorial_do 
; We have [n acc] on the stack
 acc 1    addacc -1  pacc 2 
; We have [n acc n-1] on the stack with acc=n
  pacc 2   mul
; Now [n acc n-1] on the stack with acc=n*acc
  pacc 0
; Now [n acc n-1 n*acc] on the stack
; appterm 2,4 says we have 4 items on our stack frame and we like the bottom 2, we want to ditch the reset
; So stack will be [n-1 n*acc]; and we want appterm to deliver us back to #factorial
; offcl 0 grabs the current environment and puts it in to the accumulator; appterm puts that back in env, and gets the PC from it too
; so the environment must be that for #factorial: env of {} (nothing!) and PC of #factorial
   offcl 0  appterm 2,4
    ";
    common::test_assemble_and_run::<PicoProgramU8, isize, Vec<isize>>  ( factorial, vec![10,1], 300, 10*9*8*7*6*5*4*3*2*1);
    common::test_assemble_and_run::<PicoProgramU32, isize, Vec<isize>> ( factorial, vec![10,1], 300, 10*9*8*7*6*5*4*3*2*1);
}
