extern crate picointerp;
use picointerp::*;

mod common;

#[test]
fn blah() {
    common::test_assemble_and_run::<PicoProgramU8, PicoTraceU8, isize, Vec<isize>> ( "cnst 3  pcnst 2  add", 3, 5);
    common::test_assemble_and_run::<PicoProgramU32, PicoTraceU32, isize, Vec<isize>> ( "cnst 3  pcnst 2  add", 3, 5);
}
