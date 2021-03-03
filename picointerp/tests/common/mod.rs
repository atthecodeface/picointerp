extern crate picointerp;
use self::picointerp::{PicoInterp, PicoProgram, PicoTrace, PicoValue, PicoHeap};
use self::picointerp::{PicoIRAssembler, PicoIREncoding};
pub fn test_assemble_and_run<P:PicoProgram+PicoIREncoding, T:PicoTrace<Program = P>, V:PicoValue + PartialEq, H:PicoHeap<V>>(source_code:&str, steps:usize, result:isize) {
    let mut assem = PicoIRAssembler::new();
    let mut code  = P::new();

    let pico_ir = match assem.parse(source_code) {
        Ok(x)  => x,
        Err(e) => {
            panic!("Error in assembly {}",e);
        }
    };
    println!("Disassembly:{}", pico_ir.disassemble());
    code.of_program(&pico_ir).unwrap();
        
    let mut interp = picointerp::PicoInterp::<P, V, H>::new(&code);
    let mut trace  = T::new();

    interp.set_pc(0);
    interp.run_code(&mut trace, steps);
    assert_eq!(interp.get_accumulator(),V::int(result));
}
