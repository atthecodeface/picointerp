extern crate picointerp;
use picointerp::*;

mod external;
use external::geometry;
use external::polynomial;
use external::{Value, Object, ObjModule, Pool};
// use external::geometry::{Point, Bezier};
use external::polynomial::{Poly};
type Interp<'a>  = ExtInterp::<'a, Object, Pool, PicoProgramU32, isize, Vec<isize>>;
type Module      = ObjModule::<isize>;

impl Value for isize {
}
#[test]
fn test_ext() {
    let geometry   = geometry::make_module("Geometry");
    let polynomial = polynomial::make_module("Polynomial");

    let mut toplevel = Module::new("Toplevel");
    toplevel.add_module(geometry);
    toplevel.add_module(polynomial);

    let mut assem = PicoIRAssembler::new();
    // invocation do_summat_two_ps : mut p0 p1 -> p0
    //  Polynomial::poly -> record
    let mut pico_ir = assem.parse("
             pushret -1
             acc p0@5
             pcnst 3
             pcnst 1234
             peacc Polynomial::poly
             fldget Polynomial::poly::set
             appn 3
             acc p0@5
             pcnst 2000
             peacc Polynomial::poly
             fldget Polynomial::poly::scale
             appn 2
             ret 0
        ").unwrap();

    let p0 = Poly::new();
    let p1 = Poly::new();

    let env_stack = vec!["p0", "p1"];
    let mut inv = ExtInvocation::new(&toplevel, env_stack);
    inv.resolve(&mut pico_ir).unwrap();
    assert!(pico_ir.is_resolved());

    let mut code  = PicoProgramU32::new();
    code.of_program(&pico_ir).unwrap();

    for (i,n) in code.program.iter().enumerate() {
        println!("{} : {:08x}", i, n);
    }

    let mut pool = Pool::new();
    let p0_pool = pool.add_obj(Object::of_poly(p0));
    let p1_pool = pool.add_obj(Object::of_poly(p1));
    let mut interp = Interp::new(&code, &toplevel, 0, &mut pool, &inv);
    interp.interp.stack.push( isize::of_usize(p0_pool as usize) );
    interp.interp.stack.push( isize::of_usize(p1_pool as usize) );
    let mut trace = PicoTraceStdout::new();
    interp.exec(&mut trace);

    let p0 = pool.get_obj(p0_pool).unwrap().as_poly();
    let p0 = p0.borrow();
    let p1 = pool.get_obj(p1_pool).unwrap().as_poly();
    let p1 = p1.borrow();
    println!("p0 {}",p0);
    println!("p1 {}",p1);
    // assert_eq!(interp.get_accumulator(),isize::int(200));
    assert_eq!(p0.get(0), 0.);
    assert!( (p0.get(3)-2.468).abs() < 1E-8 );
}
