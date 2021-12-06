open AutoConfig2

open Test_utils

let test_random_noalloc () =
  let test_result = test_result "Hacl.RandomBuffer.randombytes_noalloc" in
  let buf = Test_utils.init_bytes 256 in
  if Hacl.RandomBuffer.Noalloc.randombytes ~out:buf then
    test_result Success ""
  else
    test_result Failure ""

let test_random () =
  let test_result = test_result "Hacl.RandomBuffer.randombytes" in
  if Option.is_some (Hacl.RandomBuffer.randombytes ~size:128) then
    test_result Success ""
  else
    test_result Failure ""

let _ =
  Printf.printf "SHAEXT: %b\n" (has_feature SHAEXT);
  Printf.printf "AES_NI: %b\n" (has_feature AES_NI);
  Printf.printf "PCLMULQDQ: %b\n" (has_feature PCLMULQDQ);
  Printf.printf "VEC256: %b\n" (has_feature VEC256);
  Printf.printf "VEC128: %b\n" (has_feature VEC128);
  Printf.printf "BMI2: %b\n" (has_feature BMI2);
  Printf.printf "ADX: %b\n" (has_feature ADX);
  Printf.printf "SSE: %b\n" (has_feature SSE);
  Printf.printf "MOVBE: %b\n" (has_feature MOVBE);
  Printf.printf "RDRAND: %b\n" (has_feature RDRAND);

  test_random_noalloc ();
  test_random ()
