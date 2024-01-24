#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

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
