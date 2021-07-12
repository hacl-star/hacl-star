open SharedDefs

open Test_utils

type 'a hkdf_test =
  { alg: HashDefs.alg; name: string ; ikm: 'a; salt: 'a; info: 'a; expected_prk: 'a; expected_okm: 'a }

let tests = [
  {
    alg = SHA2_256;
    name = "Test 1";
    ikm = Bytes.of_string "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b";
    salt = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c";
    info = Bytes.of_string "\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9";
    expected_prk = Bytes.of_string "\x07\x77\x09\x36\x2c\x2e\x32\xdf\x0d\xdc\x3f\x0d\xc4\x7b\xba\x63\x90\xb6\xc7\x3b\xb5\x0f\x9c\x31\x22\xec\x84\x4a\xd7\xc2\xb3\xe5";
    expected_okm = Bytes.of_string "\x3c\xb2\x5f\x25\xfa\xac\xd5\x7a\x90\x43\x4f\x64\xd0\x36\x2f\x2a\x2d\x2d\x0a\x90\xcf\x1a\x5a\x4c\x5d\xb0\x2d\x56\xec\xc4\xc5\xbf\x34\x00\x72\x08\xd5\xb8\x87\x18\x58\x65"
  }
]

module MakeTests (M: SharedDefs.HKDF) = struct
  let test_noalloc (v: Bytes.t hkdf_test) name alg =
    if v.alg = alg then
      let test_result = test_result (name ^ " (noalloc) " ^ v.name) in
      let prk = Test_utils.init_bytes (Bytes.length v.expected_prk) in
      let okm = Test_utils.init_bytes (Bytes.length v.expected_okm) in
      M.Noalloc.extract ~salt:v.salt ~ikm:v.ikm ~prk;
      if not (Bytes.equal prk v.expected_prk) then
        test_result Failure "PRK mismatch";
      M.Noalloc.expand ~prk ~info:v.info ~okm;
      if not (Bytes.equal okm v.expected_okm) then
        test_result Failure "OKM mismatch";
      if Bytes.equal prk v.expected_prk &&
         Bytes.equal okm v.expected_okm then
        test_result Success ""

  let test (v: Bytes.t hkdf_test) name alg =
    let test_result = test_result (name ^ " " ^ v.name) in
    let prk = M.extract ~salt:v.salt ~ikm:v.ikm in
    let okm = M.expand ~prk ~info:v.info ~size:(Bytes.length v.expected_okm) in
    if alg = v.alg then begin
      if not (Bytes.equal prk v.expected_prk) then
        test_result Failure "PRK mismatch";
      if not (Bytes.equal okm v.expected_okm) then
        test_result Failure "OKM mismatch";
      if Bytes.equal prk v.expected_prk &&
         Bytes.equal okm v.expected_okm then
        test_result Success ""
    end else
        test_result Success "function calls"

  let run_tests name alg =
    List.iter (fun v -> test v name alg) tests;
    List.iter (fun v -> test_noalloc v name alg) tests
end

let test_agile (v: Bytes.t hkdf_test) =
  let test_result = test_result ("Agile EverCrypt.HKDF with " ^ v.name) in

  let prk = Test_utils.init_bytes (Bytes.length v.expected_prk) in
  let okm = Test_utils.init_bytes (Bytes.length v.expected_okm) in

  if EverCrypt.HMAC.is_supported_alg ~alg:v.alg then begin
    EverCrypt.HKDF.Noalloc.extract ~alg:v.alg ~salt:v.salt ~ikm:v.ikm ~prk;
    if not (Bytes.equal prk v.expected_prk) then
      test_result Failure "PRK mismatch";
    EverCrypt.HKDF.Noalloc.expand ~alg:v.alg ~prk ~info:v.info ~okm;
    if not (Bytes.equal okm v.expected_okm) then
      test_result Failure "OKM mismatch";
    if Bytes.equal prk v.expected_prk &&
       Bytes.equal okm v.expected_okm then
      test_result Success ""
  end
  else
    test_result Failure "hash algorithm reported as not supported"


(* TODO: find tests for the other hash functions
   Only HKDF_SHA2_256 is currently covered by a unit tests. As a sanity check,
   function calls for all the other versions are being exercised, but
   their output is not checked.
*)
let _ =
  List.iter test_agile tests;

  let module Tests = MakeTests (EverCrypt.HKDF_SHA2_256) in
  Tests.run_tests "EverCrypt.HKDF_SHA2_256" SHA2_256;

  let module Tests = MakeTests (EverCrypt.HKDF_SHA2_384) in
  Tests.run_tests "EverCrypt.HKDF_SHA2_384" SHA2_384;

  let module Tests = MakeTests (EverCrypt.HKDF_SHA2_512) in
  Tests.run_tests "EverCrypt.HKDF_SHA2_512" SHA2_512;

  let module Tests = MakeTests (Hacl.HKDF_SHA2_256) in
  Tests.run_tests "Hacl.HKDF_SHA2_256" SHA2_256;

  let module Tests = MakeTests (Hacl.HKDF_SHA2_512) in
  Tests.run_tests "Hacl.HKDF_SHA2_512" SHA2_512;

  let module Tests = MakeTests (Hacl.HKDF_BLAKE2b) in
  Tests.run_tests "Hacl.HKDF_BLAKE2b" BLAKE2b;

  let module Tests = MakeTests (Hacl.HKDF_BLAKE2s) in
  Tests.run_tests "Hacl.HKDF_BLAKE2s" BLAKE2s
