open Test_utils

(* TODO: add some more pertinent tests *)
let _ =
  let print_result = print_result "EverCrypt.DRBG" in
  match EverCrypt.DRBG.instantiate EverCrypt.Hash.SHA2_512 ~personalization_string:(Bigstring.create 128) with
  | Some st ->
    if EverCrypt.DRBG.reseed st ~additional_input:(Bigstring.create 128) then
      let output = Bigstring.create 1024 in
      if EverCrypt.DRBG.generate st output ~additional_input:(Bigstring.create 128) then begin
        print_result "Success";
        EverCrypt.DRBG.uninstantiate st
      end
      else
        print_result "Generation failure"
    else
      print_result "Reseed failure"
  | None -> print_result "Initialization failure"
