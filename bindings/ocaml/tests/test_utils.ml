open QCheck2
open EverCrypt.Error

type result =
  | Success
  | Failure
  | Skipped

let test_result t res r =
  let r = if r <> "" then
      Printf.sprintf ": %s" r
    else
      ""
  in
  match res with
  | Success -> Printf.printf "[%s] Success%s\n" t r
  | Failure -> failwith (Printf.sprintf "[%s] Failure%s" t r)
  | Skipped -> Printf.printf "[%s] Skipped%s\n" t r

let print_error = function
  | UnsupportedAlgorithm -> "Unsupported algorithm"
  | InvalidKey -> "Invalid key"
  | AuthenticationFailure -> "Authentication failure"
  | InvalidIVLength -> "Invalid IV length"
  | DecodeError -> "Decode error"
  | MaximumLengthExceeded -> "Maximum length exceeded"

let init_bytes len =
  let buf = Bytes.create len in
  Bytes.fill buf 0 len '\x00';
  buf

let rec supports = function
  | [] -> true
  | f::fs -> AutoConfig2.has_feature f && supports fs

let make_qcheck_test ?(count=100) ?print (gen: 'a Gen.t) (f: 'a -> bool) () =
  Test.(check_exn @@ make ~count ?print gen f)

let bytes_of_hex hex = Cstruct.(to_bytes (of_hex hex))
