open EverCrypt.Error

type result =
  | Success
  | Failure

let test_result t res r =
  let r = if r <> "" then
      Printf.sprintf ": %s" r
    else
      ""
  in
  match res with
  | Success -> Printf.printf "[%s] Success%s\n" t r
  | Failure -> failwith (Printf.sprintf "[%s] Failure%s" t r)

let print_error = function
  | UnsupportedAlgorithm -> "Unsupported algorithm"
  | InvalidKey -> "Invalid key"
  | AuthenticationFailure -> "Authentication failure"
  | InvalidIVLength -> "Invalid IV length"
  | DecodeError -> "Decode error"

let init_bytes len =
  let buf = Bytes.create len in
  Bytes.fill buf 0 len '\x00';
  buf
