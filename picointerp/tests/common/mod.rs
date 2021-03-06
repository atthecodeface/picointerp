extern crate picointerp;
use self::picointerp::{PicoInterp, PicoProgram, PicoTrace, PicoValue, PicoHeap, PicoStack};
use self::picointerp::{PicoTraceStdout};
use self::picointerp::{PicoIRAssembler, PicoIREncoding};
pub fn test_assemble_and_run<P:PicoProgram+PicoIREncoding, V:PicoValue + PartialEq, H:PicoHeap<V>>(source_code:&str, inputs:Vec<isize>, steps:usize, result:isize) {
    let mut assem = PicoIRAssembler::new();
    let mut code  = P::new();

    let mut pico_ir = match assem.parse(source_code) {
        Ok(x)  => x,
        Err(e) => {
            panic!("Error in assembly {}",e);
        }
    };

    pico_ir.resolve(&|a,b| None);

    println!("Disassembly:{}", pico_ir.disassemble());

    assert!(pico_ir.is_resolved());

    code.of_program(&pico_ir).unwrap();
        
    let mut interp = picointerp::PicoInterp::<P, V, H>::new(&code);
    let mut trace  = PicoTraceStdout::new();

    interp.set_pc(0);
    for i in inputs {
        interp.stack.push(V::int(i));
    }
    interp.run_code(&mut trace, steps);
    assert_eq!(interp.get_accumulator(),V::int(result));
}
