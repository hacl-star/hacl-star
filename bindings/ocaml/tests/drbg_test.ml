open Test_utils

(* TODO: add some more pertinent tests *)
let _ =
  let test_result = test_result "EverCrypt.DRBG" in
  match EverCrypt.DRBG.instantiate EverCrypt.Hash.SHA2_512 ~personalization_string:(Bigstring.create 128) with
  | Some st ->
    if EverCrypt.DRBG.reseed st ~additional_input:(Bigstring.create 128) then
      let output = Bigstring.create 1024 in
      if EverCrypt.DRBG.generate st output ~additional_input:(Bigstring.create 128) then begin
        test_result Success "";
        EverCrypt.DRBG.uninstantiate st
      end
      else
        test_result Failure "Generation failure"
    else
      test_result Failure "Reseed failure"
  | None -> test_result Failure "Initialization failure"
