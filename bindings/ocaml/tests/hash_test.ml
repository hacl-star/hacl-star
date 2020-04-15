open EverCrypt
open SharedDefs

open Test_utils

type alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA3_224
  | SHA3_256
  | SHA3_384
  | SHA3_512
  | SHA1
  | MD5

type 'a hash_test =
  { name: string; alg: alg; plaintext: 'a; expected: 'a }

let test_sha2_224 : Bytes.t hash_test =
  {
    name = "SHA2_224 Test 1";
    alg = SHA2_224;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\x23\x09\x7d\x22\x34\x05\xd8\x22\x86\x42\xa4\x77\xbd\xa2\x55\xb3\x2a\xad\xbc\xe4\xbd\xa0\xb3\xf7\xe3\x6c\x9d\xa7"
}

let test_sha2_256 : Bytes.t hash_test =
  {
    name = "SHA2_256 Test 1";
    alg = SHA2_256;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xba\x78\x16\xbf\x8f\x01\xcf\xea\x41\x41\x40\xde\x5d\xae\x22\x23\xb0\x03\x61\xa3\x96\x17\x7a\x9c\xb4\x10\xff\x61\xf2\x00\x15\xad"
}

let test_sha2_384 : Bytes.t hash_test =
  {
    name = "SHA2_384 Test 1";
    alg = SHA2_384;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xcb\x00\x75\x3f\x45\xa3\x5e\x8b\xb5\xa0\x3d\x69\x9a\xc6\x50\x07\x27\x2c\x32\xab\x0e\xde\xd1\x63\x1a\x8b\x60\x5a\x43\xff\x5b\xed\x80\x86\x07\x2b\xa1\xe7\xcc\x23\x58\xba\xec\xa1\x34\xc8\x25\xa7"
}

let test_sha2_512 : Bytes.t hash_test =
  {
    name = "SHA2_512 Test 1";
    alg = SHA2_512;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xdd\xaf\x35\xa1\x93\x61\x7a\xba\xcc\x41\x73\x49\xae\x20\x41\x31\x12\xe6\xfa\x4e\x89\xa9\x7e\xa2\x0a\x9e\xee\xe6\x4b\x55\xd3\x9a\x21\x92\x99\x2a\x27\x4f\xc1\xa8\x36\xba\x3c\x23\xa3\xfe\xeb\xbd\x45\x4d\x44\x23\x64\x3c\xe8\x0e\x2a\x9a\xc9\x4f\xa5\x4c\xa4\x9f"
}

let test_sha3_224 : Bytes.t hash_test =
  {
    name = "SHA3_224 Test 1";
    alg = SHA3_224;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xe6\x42\x82\x4c\x3f\x8c\xf2\x4a\xd0\x92\x34\xee\x7d\x3c\x76\x6f\xc9\xa3\xa5\x16\x8d\x0c\x94\xad\x73\xb4\x6f\xdf"
}

let test_sha3_256 : Bytes.t hash_test =
  {
    name = "SHA3_256 Test 1";
    alg = SHA3_256;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\x3a\x98\x5d\xa7\x4f\xe2\x25\xb2\x04\x5c\x17\x2d\x6b\xd3\x90\xbd\x85\x5f\x08\x6e\x3e\x9d\x52\x5b\x46\xbf\xe2\x45\x11\x43\x15\x32"
}

let test_sha3_384 : Bytes.t hash_test =
  {
    name = "SHA3_384 Test 1";
    alg = SHA3_384;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xec\x01\x49\x82\x88\x51\x6f\xc9\x26\x45\x9f\x58\xe2\xc6\xad\x8d\xf9\xb4\x73\xcb\x0f\xc0\x8c\x25\x96\xda\x7c\xf0\xe4\x9b\xe4\xb2\x98\xd8\x8c\xea\x92\x7a\xc7\xf5\x39\xf1\xed\xf2\x28\x37\x6d\x25"
}

let test_sha3_512 : Bytes.t hash_test =
  {
    name = "SHA3_512 Test 1";
    alg = SHA3_512;
    plaintext = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xb7\x51\x85\x0b\x1a\x57\x16\x8a\x56\x93\xcd\x92\x4b\x6b\x09\x6e\x08\xf6\x21\x82\x74\x44\xf7\x0d\x88\x4f\x5d\x02\x40\xd2\x71\x2e\x10\xe1\x16\xe9\x19\x2a\xf3\xc9\x1a\x7e\xc5\x76\x47\xe3\x93\x40\x57\x34\x0b\x4c\xf4\x08\xd5\xa5\x65\x92\xf8\x27\x4e\xec\x53\xf0"
}

let test_sha1 : Bytes.t hash_test =
  {
    name = "SHA1 Test 1";
    alg = SHA1;
    plaintext = Bytes.of_string "\x54\x9e\x95\x9e";
    expected = Bytes.of_string "\xb7\x8b\xae\x6d\x14\x33\x8f\xfc\xcf\xd5\xd5\xb5\x67\x4a\x27\x5f\x6e\xf9\xc7\x17"
}

let test_md5 : Bytes.t hash_test =
  {
    name = "MD5 Test 1";
    alg = MD5;
    plaintext = Bytes.of_string "\x6d\x65\x73\x73\x61\x67\x65\x20\x64\x69\x67\x65\x73\x74";
    expected = Bytes.of_string "\xf9\x6b\x69\x7d\x7c\xb7\x93\x8d\x52\x5a\x2f\x31\xaa\xf1\x61\xd0"
}

let alg_definition = function
  | SHA2_224 -> HashDefs.SHA2_224
  | SHA2_256 -> HashDefs.SHA2_256
  | SHA2_384 -> HashDefs.SHA2_384
  | SHA2_512 -> HashDefs.SHA2_512
  | SHA1 -> HashDefs.Legacy HashDefs.SHA1
  | MD5 -> HashDefs.Legacy HashDefs.MD5
  | _ -> failwith "Algorithm not supported in agile Hashing API"

let output_len = function
  | SHA2_224
  | SHA3_224 -> 28
  | SHA2_256
  | SHA3_256 -> 32
  | SHA2_384
  | SHA3_384 -> 48
  | SHA2_512
  | SHA3_512 -> 64
  | SHA1 -> 20
  | MD5 -> 16

let test_agile (v: Bytes.t hash_test) =
  let test_result = test_result ("Hash " ^ v.name)  in
  let alg = alg_definition v.alg in
  let output = Test_utils.init_bytes (output_len v.alg) in

  Hash.hash alg output v.plaintext;
  if Bytes.compare output v.expected = 0 then
    test_result Success "one-shot hash"
  else
    test_result Failure "one-shot hash";

  let st = Hash.init (alg_definition v.alg) in
  Hash.update st v.plaintext;
  Hash.finish st output;
  if Bytes.compare output v.expected = 0 then
    test_result Success "incremental hash"
  else
    test_result Failure "incremental hash"

let test_nonagile (n: string) (v: Bytes.t hash_test) hash =
  let test_result = test_result (n ^ "." ^ v.name) in
  let output = Test_utils.init_bytes (output_len v.alg) in
  hash v.plaintext output;
  if Bytes.compare output v.expected = 0 then
    test_result Success ""
  else
    test_result Failure ""

let test_keccak () =
  let v = test_sha3_256 in
  let test_result = test_result "Keccak" in
  let sha3_256 = Hacl.Keccak.keccak 1088 512 (Char.code '\x06') in
  let output = Test_utils.init_bytes 32 in
  sha3_256 v.plaintext output;

  let output_shake128 = Test_utils.init_bytes 16 in
  Hacl.Keccak.shake128 v.plaintext output_shake128;

  let keccak_128 = Hacl.Keccak.keccak 1344 256 (Char.code '\x1f') in
  let output_keccak_128 = Test_utils.init_bytes 16 in
  keccak_128 v.plaintext output_keccak_128;

  let output_shake256 = Test_utils.init_bytes 32 in
  Hacl.Keccak.shake256 v.plaintext output_shake256;

  let keccak_256 = Hacl.Keccak.keccak 1088 512 (Char.code '\x1f') in
  let output_keccak_256 = Test_utils.init_bytes 32 in
  keccak_256 v.plaintext output_keccak_256;

  if Bytes.compare output v.expected = 0 &&
     Bytes.compare output_shake128 output_keccak_128 = 0 &&
     Bytes.compare output_shake256 output_keccak_256 = 0 then
    test_result Success ""
  else
    test_result Failure ""


let _ =
  test_agile test_sha2_224;
  test_agile test_sha2_256;
  test_agile test_sha2_384;
  test_agile test_sha2_512;

  test_nonagile "Hacl" test_sha2_224 Hacl.SHA2_224.hash;
  test_nonagile "Hacl" test_sha2_256 Hacl.SHA2_256.hash;
  test_nonagile "Hacl" test_sha2_384 Hacl.SHA2_384.hash;
  test_nonagile "Hacl" test_sha2_512 Hacl.SHA2_512.hash;

  test_nonagile "Hacl" test_sha3_224 Hacl.SHA3_224.hash;
  test_nonagile "Hacl" test_sha3_256 Hacl.SHA3_256.hash;
  test_nonagile "Hacl" test_sha3_384 Hacl.SHA3_384.hash;
  test_nonagile "Hacl" test_sha3_512 Hacl.SHA3_512.hash;

  test_nonagile "EverCrypt" test_sha2_224 EverCrypt.SHA2_224.hash;
  test_nonagile "EverCrypt" test_sha2_256 EverCrypt.SHA2_256.hash;

  test_agile test_sha1;
  test_agile test_md5;

  test_nonagile "Hacl" test_sha1 Hacl.SHA1.hash;
  test_nonagile "Hacl" test_md5 Hacl.MD5.hash;

  test_keccak ()
