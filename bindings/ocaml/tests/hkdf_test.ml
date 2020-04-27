open SharedDefs

open Test_utils

type 'a hkdf_test =
  { alg: HashDefs.alg; name: string ; ikm: 'a; salt: 'a; info: 'a; expected_prk: 'a; expected_okm: 'a }

let tests = [
  {
    alg = SHA2_256;
    name = "SHA2_256 Test 1";
    ikm = Bytes.of_string "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b";
    salt = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c";
    info = Bytes.of_string "\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9";
    expected_prk = Bytes.of_string "\x07\x77\x09\x36\x2c\x2e\x32\xdf\x0d\xdc\x3f\x0d\xc4\x7b\xba\x63\x90\xb6\xc7\x3b\xb5\x0f\x9c\x31\x22\xec\x84\x4a\xd7\xc2\xb3\xe5";
    expected_okm = Bytes.of_string "\x3c\xb2\x5f\x25\xfa\xac\xd5\x7a\x90\x43\x4f\x64\xd0\x36\x2f\x2a\x2d\x2d\x0a\x90\xcf\x1a\x5a\x4c\x5d\xb0\x2d\x56\xec\xc4\xc5\xbf\x34\x00\x72\x08\xd5\xb8\x87\x18\x58\x65"
  }
]

let test_agile (v: Bytes.t hkdf_test) =
  let test_result = test_result ("Agile EverCrypt.HKDF with " ^ v.name) in

  let prk = Test_utils.init_bytes (Bytes.length v.expected_prk) in
  let okm = Test_utils.init_bytes (Bytes.length v.expected_okm) in

  if EverCrypt.HMAC.is_supported_alg v.alg then begin
    EverCrypt.HKDF.extract v.alg prk v.salt v.ikm;
    if Bytes.compare prk v.expected_prk <> 0 then
      test_result Failure "PRK mismatch";
    EverCrypt.HKDF.expand v.alg okm v.expected_prk v.info;
    if Bytes.compare okm v.expected_okm <> 0 then
      test_result Failure "OKM mismatch";
    if Bytes.compare prk v.expected_prk = 0 && Bytes.compare okm v.expected_okm = 0 then
      test_result Success ""
  end
  else
    test_result Failure "hash algorithm reported as not supported"

let test_nonagile (v: Bytes.t hkdf_test) t alg expand extract =
  if v.alg = alg then
    let test_result = test_result (t ^ "_" ^ v.name) in

  let prk = Test_utils.init_bytes (Bytes.length v.expected_prk) in
  let okm = Test_utils.init_bytes (Bytes.length v.expected_okm) in

  extract prk v.salt v.ikm;
  if Bytes.compare prk v.expected_prk <> 0 then
    test_result Failure "PRK mismatch";
  expand okm v.expected_prk v.info;
  if Bytes.compare okm v.expected_okm <> 0 then
    test_result Failure "OKM mismatch";
  if Bytes.compare prk v.expected_prk = 0 && Bytes.compare okm v.expected_okm = 0 then
    test_result Success ""


(* TODO: find tests for the other hash functions *)
let _ =
  List.iter test_agile tests;
  List.iter (fun v -> test_nonagile v "EverCrypt.HKDF" SHA2_256 EverCrypt.HKDF_SHA2_256.expand EverCrypt.HKDF_SHA2_256.extract) tests;
  List.iter (fun v -> test_nonagile v "Hacl.HKDF" SHA2_256 Hacl.HKDF_SHA2_256.expand Hacl.HKDF_SHA2_256.extract) tests
