#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[derive(PartialEq, Clone, Copy)]
pub enum error_code
{
    Success,
    UnsupportedAlgorithm,
    InvalidKey,
    AuthenticationFailure,
    InvalidIVLength,
    DecodeError,
    MaximumLengthExceeded
}
