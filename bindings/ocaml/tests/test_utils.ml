open EverCrypt.Error

let print_result t r = Printf.printf "[%s] %s\n" t r

let print_error = function
  | UnsupportedAlgorithm -> "Unsupported algorithm"
  | InvalidKey -> "Invalid key"
  | AuthenticationFailure -> "Authentication failure"
  | InvalidIVLength -> "Invalid IV length"
  | DecodeError -> "Decode error"
