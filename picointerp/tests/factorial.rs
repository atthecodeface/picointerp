extern crate picointerp;
use picointerp::*;

mod common;

#[test]
fn blah() {
    //   this is called with 2 arguments
    //   It has 0 vars and 1 function so creates a closure of (factorial, {arg}*0, {Infix, pc}*(1-1)) which it pushes
    //   It also leaves this in the accumulator
    //   It has 1 function so it creates no more infix objects (subobjects of the closure) - these would be pushed
    // closurerec 1, 0, factorial
    // acc 0 // this is null 
    //   closure X, ! 1 ! pushes accumulator to stack first
    // closure L2, 1
    // push
    // acc 1
    // push
    // makeblock 2, 0
    // pop 2
    //   stack is now XX XX {run_me, factorial}
    // const "Shm/112"
    // push
    // getglobal Toploop!
    // getfield 1
    //   stack is now XX XX {run_me, factorial} "Shm/112" Toploop!.1
    // appterm 2, 3
    // restart
    //      let rec factorial acc n = if n<1 then acc else factorial (acc*n) (n-1)
        let factorial = "
clos 0, factorial appn 2
#loop br loop
#factorial     grab 1   acc 1      pacc 0  cnst 1  cmpgt   bne factorial_do   acc 0 ret 2
#factorial_do  acc 1    addacc -1  pacc 0  acc 2   pacc 0  acc 2   mul   pacc 0   offcl 0  appterm 2,4
    ";
    common::test_assemble_and_run::<PicoProgramU8, isize, Vec<isize>>  ( factorial, vec![10,1], 300, 10*9*8*7*6*5*4*3*2*1);
    common::test_assemble_and_run::<PicoProgramU32, isize, Vec<isize>> ( factorial, vec![10,1], 300, 10*9*8*7*6*5*4*3*2*1);
}
