module EverCrypt.Error

/// The unified EverCrypt error type, to be used by all (new) implementations.
/// --------------------------------------------------------------------------

type error_code =
| Success
| UnsupportedAlgorithm
| InvalidKey
| AuthenticationFailure
| InvalidIVLength

let _: squash (inversion error_code) = allow_inversion error_code
