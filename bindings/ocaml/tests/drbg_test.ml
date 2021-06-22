open Test_utils
open SharedDefs.HashDefs

let test name alg =
  let test_result = test_result ("EverCrypt.DRBG with " ^ name) in
  assert (EverCrypt.DRBG.is_supported_alg alg);
  match EverCrypt.DRBG.instantiate alg ~personalization_string:(init_bytes 128) with
  | Some st ->
    (* reseeding is optional, it is included here for testing purposes *)
    if EverCrypt.DRBG.reseed st ~additional_input:(init_bytes 128) then
      let output1 = init_bytes 1024 in
      let output2 = init_bytes 1024 in
      if EverCrypt.DRBG.Noalloc.generate st output1 ~additional_input:(init_bytes 128) &&
         EverCrypt.DRBG.Noalloc.generate st output2 then
        assert (output1 <> output2)
      else
        test_result Failure "Generation failure (noalloc)"
    else
      test_result Failure "Reseed failure";
    (match EverCrypt.DRBG.generate st 512 with
    | Some output ->
       assert (Bytes.length output = 512)
    | None ->
      test_result Failure "Generation failure");
    test_result Success ""
  | None -> test_result Failure "Initialization failure"

let _ =
  test "SHA2_256" SHA2_256;
  test "SHA2_384" SHA2_384;
  test "SHA2_512" SHA2_512
