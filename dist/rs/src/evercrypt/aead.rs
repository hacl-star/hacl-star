#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub struct state_s { pub impl: crate::hacl::spec::impl, pub ek: Box<[u8]> }

pub fn uu___is_Ek(a: crate::hacl::spec::alg, projectee: state_s) -> bool
{
    crate::lowstar::ignore::ignore::<crate::hacl::spec::alg>(a);
    crate::lowstar::ignore::ignore::<state_s>(projectee);
    true
}
