open Test_utils

(* TODO: add some more pertinent tests *)
let _ =
  let test_result = test_result "EverCrypt.DRBG" in
  match EverCrypt.DRBG.instantiate SHA2_512 ~personalization_string:(init_bytes 128) with
  | Some st ->
    if EverCrypt.DRBG.reseed st ~additional_input:(init_bytes 128) then
      let output = init_bytes 1024 in
      if EverCrypt.DRBG.generate st output ~additional_input:(init_bytes 128) then begin
        test_result Success "";
        EverCrypt.DRBG.uninstantiate st
      end
      else
        test_result Failure "Generation failure"
    else
      test_result Failure "Reseed failure"
  | None -> test_result Failure "Initialization failure"
