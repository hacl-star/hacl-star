open Test_utils
open AutoConfig2

type 'a curve25519_test =
  { name : string ; scalar: 'a ; point : 'a ; expected : 'a }

let tests = [
  {
    name = "Test 1";
    scalar = Bytes.of_string "\xa5\x46\xe3\x6b\xf0\x52\x7c\x9d\x3b\x16\x15\x4b\x82\x46\x5e\xdd\x62\x14\x4c\x0a\xc1\xfc\x5a\x18\x50\x6a\x22\x44\xba\x44\x9a\xc4";
    point = Bytes.of_string "\xe6\xdb\x68\x67\x58\x30\x30\xdb\x35\x94\xc1\xa4\x24\xb1\x5f\x7c\x72\x66\x24\xec\x26\xb3\x35\x3b\x10\xa9\x03\xa6\xd0\xab\x1c\x4c";
    expected = Bytes.of_string "\xc3\xda\x55\x37\x9d\xe9\xc6\x90\x8e\x94\xea\x4d\xf2\x8d\x08\x4f\x32\xec\xcf\x03\x49\x1c\x71\xf7\x54\xb4\x07\x55\x77\xa2\x85\x52"
  };
  {
    name = "Test 2";
    scalar = Bytes.of_string "\x4b\x66\xe9\xd4\xd1\xb4\x67\x3c\x5a\xd2\x26\x91\x95\x7d\x6a\xf5\xc1\x1b\x64\x21\xe0\xea\x01\xd4\x2c\xa4\x16\x9e\x79\x18\xba\x0d";
    point = Bytes.of_string "\xe5\x21\x0f\x12\x78\x68\x11\xd3\xf4\xb7\x95\x9d\x05\x38\xae\x2c\x31\xdb\xe7\x10\x6f\xc0\x3c\x3e\xfc\x4c\xd5\x49\xc7\x15\xa4\x93";
    expected = Bytes.of_string "\x95\xcb\xde\x94\x76\xe8\x90\x7d\x7a\xad\xe4\x5c\xb4\xb8\x73\xf8\x8b\x59\x5a\x68\x79\x9f\xa1\x52\xe6\xf8\xf7\x64\x7a\xac\x79\x57"
  }
]

let basepoint = Bytes.init 32 (function 0 -> '\x09' | _ -> '\x00')

module MakeTests (M: SharedDefs.Curve25519) = struct
  let test_noalloc v t reqs =
    let test_result = test_result (t ^ ".Noalloc " ^ v.name) in
    if supports reqs then begin
      let out_scalarmult = Test_utils.init_bytes 32 in
      let out_ecdh = Test_utils.init_bytes 32 in

      let pk = Test_utils.init_bytes 32 in
      M.Noalloc.scalarmult ~scalar:v.scalar ~point:basepoint ~result:pk;
      let pk2 = Test_utils.init_bytes 32 in
      M.Noalloc.secret_to_public ~sk:v.scalar ~pk:pk2;
      if not (Bytes.equal pk pk2) then
        test_result Failure "secret_to_public failure";

      M.Noalloc.scalarmult ~scalar:v.scalar ~point:v.point ~result:out_scalarmult;
      if M.Noalloc.ecdh ~sk:v.scalar ~pk:v.point ~shared:out_ecdh then
        if Bytes.equal out_scalarmult v.expected && Bytes.equal out_ecdh v.expected then
          test_result Success ""
        else
          test_result Failure "ECDH shared scret mismatch"
      else
        test_result Failure "ECDH failure"
    end else
      test_result Skipped "Required CPU feature not detected"

  let test v t reqs =
    let test_result = test_result (t ^ " " ^ v.name) in
    if supports reqs then begin
      let pk = M.scalarmult ~scalar:v.scalar ~point:basepoint in
      let pk2 = M.secret_to_public ~sk:v.scalar in
      if not (Bytes.equal pk pk2) then
        test_result Failure "secret_to_public failure";

      let out_scalarmult = M.scalarmult ~scalar:v.scalar ~point:v.point in
      match M.ecdh ~sk:v.scalar ~pk:v.point with
      | Some out_ecdh ->
        if Bytes.equal out_scalarmult v.expected && Bytes.equal out_ecdh v.expected then
          test_result Success ""
        else
          test_result Failure "ECDH shared scret mismatch"
      | None ->
        test_result Failure "ECDH failure"
    end else
      test_result Skipped "Required CPU feature not detected"

  let run_tests name reqs =
    List.iter (fun v -> test_noalloc v name reqs) tests;
    List.iter (fun v -> test v name reqs) tests
end

let _ =
  let module Tests = MakeTests (EverCrypt.Curve25519) in
  Tests.run_tests "EverCrypt.Curve25519" [];

  let module Tests = MakeTests (Hacl.Curve25519_51) in
  Tests.run_tests "Hacl.Curve25519_51" [];

  let module Tests = MakeTests (Hacl.Curve25519_64) in
  Tests.run_tests "Hacl.Curve25519_64" [BMI2; ADX]
