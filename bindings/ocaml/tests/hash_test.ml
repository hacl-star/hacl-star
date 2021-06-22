open EverCrypt
open SharedDefs
open AutoConfig2

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
  | Keccak_256
  | BLAKE2b
  | BLAKE2s
  | SHA1
  | MD5

type 'a hash_test =
  { name: string; alg: alg; msg: 'a; expected: 'a }

let test_sha2_224 : Bytes.t hash_test =
  {
    name = "SHA2_224 Test 1";
    alg = SHA2_224;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\x23\x09\x7d\x22\x34\x05\xd8\x22\x86\x42\xa4\x77\xbd\xa2\x55\xb3\x2a\xad\xbc\xe4\xbd\xa0\xb3\xf7\xe3\x6c\x9d\xa7"
}

let test_sha2_256 : Bytes.t hash_test =
  {
    name = "SHA2_256 Test 1";
    alg = SHA2_256;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xba\x78\x16\xbf\x8f\x01\xcf\xea\x41\x41\x40\xde\x5d\xae\x22\x23\xb0\x03\x61\xa3\x96\x17\x7a\x9c\xb4\x10\xff\x61\xf2\x00\x15\xad"
}

let test_sha2_384 : Bytes.t hash_test =
  {
    name = "SHA2_384 Test 1";
    alg = SHA2_384;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xcb\x00\x75\x3f\x45\xa3\x5e\x8b\xb5\xa0\x3d\x69\x9a\xc6\x50\x07\x27\x2c\x32\xab\x0e\xde\xd1\x63\x1a\x8b\x60\x5a\x43\xff\x5b\xed\x80\x86\x07\x2b\xa1\xe7\xcc\x23\x58\xba\xec\xa1\x34\xc8\x25\xa7"
}

let test_sha2_512 : Bytes.t hash_test =
  {
    name = "SHA2_512 Test 1";
    alg = SHA2_512;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xdd\xaf\x35\xa1\x93\x61\x7a\xba\xcc\x41\x73\x49\xae\x20\x41\x31\x12\xe6\xfa\x4e\x89\xa9\x7e\xa2\x0a\x9e\xee\xe6\x4b\x55\xd3\x9a\x21\x92\x99\x2a\x27\x4f\xc1\xa8\x36\xba\x3c\x23\xa3\xfe\xeb\xbd\x45\x4d\x44\x23\x64\x3c\xe8\x0e\x2a\x9a\xc9\x4f\xa5\x4c\xa4\x9f"
}

let test_sha3_224 : Bytes.t hash_test =
  {
    name = "SHA3_224 Test 1";
    alg = SHA3_224;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xe6\x42\x82\x4c\x3f\x8c\xf2\x4a\xd0\x92\x34\xee\x7d\x3c\x76\x6f\xc9\xa3\xa5\x16\x8d\x0c\x94\xad\x73\xb4\x6f\xdf"
}

let test_sha3_256 : Bytes.t hash_test =
  {
    name = "SHA3_256 Test 1";
    alg = SHA3_256;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\x3a\x98\x5d\xa7\x4f\xe2\x25\xb2\x04\x5c\x17\x2d\x6b\xd3\x90\xbd\x85\x5f\x08\x6e\x3e\x9d\x52\x5b\x46\xbf\xe2\x45\x11\x43\x15\x32"
}

let test_sha3_384 : Bytes.t hash_test =
  {
    name = "SHA3_384 Test 1";
    alg = SHA3_384;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xec\x01\x49\x82\x88\x51\x6f\xc9\x26\x45\x9f\x58\xe2\xc6\xad\x8d\xf9\xb4\x73\xcb\x0f\xc0\x8c\x25\x96\xda\x7c\xf0\xe4\x9b\xe4\xb2\x98\xd8\x8c\xea\x92\x7a\xc7\xf5\x39\xf1\xed\xf2\x28\x37\x6d\x25"
}

let test_sha3_512 : Bytes.t hash_test =
  {
    name = "SHA3_512 Test 1";
    alg = SHA3_512;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\xb7\x51\x85\x0b\x1a\x57\x16\x8a\x56\x93\xcd\x92\x4b\x6b\x09\x6e\x08\xf6\x21\x82\x74\x44\xf7\x0d\x88\x4f\x5d\x02\x40\xd2\x71\x2e\x10\xe1\x16\xe9\x19\x2a\xf3\xc9\x1a\x7e\xc5\x76\x47\xe3\x93\x40\x57\x34\x0b\x4c\xf4\x08\xd5\xa5\x65\x92\xf8\x27\x4e\xec\x53\xf0"
}

let test_blake2b : Bytes.t hash_test =
  {
    name = "BLAKE2b Test 1";
    alg = BLAKE2b;
    msg = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\x5c\x5d\x5e\x5f";
    expected = Bytes.of_string "\x1c\x07\x7e\x27\x9d\xe6\x54\x85\x23\x50\x2b\x6d\xf8\x00\xff\xda\xb5\xe2\xc3\xe9\x44\x2e\xb8\x38\xf5\x8c\x29\x5f\x3b\x14\x7c\xef\x9d\x70\x1c\x41\xc3\x21\x28\x3f\x00\xc7\x1a\xff\xa0\x61\x93\x10\x39\x91\x26\x29\x5b\x78\xdd\x4d\x1a\x74\x57\x2e\xf9\xed\x51\x35"
  }

let test_blake2s : Bytes.t hash_test =
  {
    name = "BLAKE2s Test 1";
    alg = BLAKE2s;
    msg = Bytes.of_string "\x61\x62\x63";
    expected = Bytes.of_string "\x50\x8C\x5E\x8C\x32\x7C\x14\xE2\xE1\xA7\x2B\xA3\x4E\xEB\x45\x2F\x37\x45\x8B\x20\x9E\xD6\x3A\x29\x4D\x99\x9B\x4C\x86\x67\x59\x82"
  }

let test_sha1 : Bytes.t hash_test =
  {
    name = "SHA1 Test 1";
    alg = SHA1;
    msg = Bytes.of_string "\x54\x9e\x95\x9e";
    expected = Bytes.of_string "\xb7\x8b\xae\x6d\x14\x33\x8f\xfc\xcf\xd5\xd5\xb5\x67\x4a\x27\x5f\x6e\xf9\xc7\x17"
}

let test_md5 : Bytes.t hash_test =
  {
    name = "MD5 Test 1";
    alg = MD5;
    msg = Bytes.of_string "\x6d\x65\x73\x73\x61\x67\x65\x20\x64\x69\x67\x65\x73\x74";
    expected = Bytes.of_string "\xf9\x6b\x69\x7d\x7c\xb7\x93\x8d\x52\x5a\x2f\x31\xaa\xf1\x61\xd0"
}

type 'a blake2_keyed_test =
  { name: string; msg: 'a; key: 'a; expected: 'a }

let blake2b_keyed_tests = [
  {
    name = "Test 1";
    msg = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b";
    key = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f";
    expected = Bytes.of_string "\xc8\xf6\x8e\x69\x6e\xd2\x82\x42\xbf\x99\x7f\x5b\x3b\x34\x95\x95\x08\xe4\x2d\x61\x38\x10\xf1\xe2\xa4\x35\xc9\x6e\xd2\xff\x56\x0c\x70\x22\xf3\x61\xa9\x23\x4b\x98\x37\xfe\xee\x90\xbf\x47\x92\x2e\xe0\xfd\x5f\x8d\xdf\x82\x37\x18\xd8\x6d\x1e\x16\xc6\x09\x00\x71"
  }
]

let blake2s_keyed_tests = [
  {
    name = "Test 1";
    msg = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e";
    key = Bytes.of_string "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f";
    expected = Bytes.of_string "\xc6\x53\x82\x51\x3f\x07\x46\x0d\xa3\x98\x33\xcb\x66\x6c\x5e\xd8\x2e\x61\xb9\xe9\x98\xf4\xb0\xc4\x28\x7c\xee\x56\xc3\xcc\x9b\xcd"
  }
]

(* Source: https://bob.nem.ninja/test-vectors.html *)
let keccak256_test =
  {
    name = "Test 1";
    alg = Keccak_256;
    msg = Bytes.of_string "\xcc";
    expected = Bytes.of_string "\xee\xad\x6d\xbf\xc7\x34\x0a\x56\xca\xed\xc0\x44\x69\x6a\x16\x88\x70\x54\x9a\x6a\x7f\x6f\x56\x96\x1e\x84\xa5\x4b\xd9\x97\x0b\x8a"
  }


let alg_definition = function
  | SHA2_224 -> HashDefs.SHA2_224
  | SHA2_256 -> HashDefs.SHA2_256
  | SHA2_384 -> HashDefs.SHA2_384
  | SHA2_512 -> HashDefs.SHA2_512
  | BLAKE2b -> HashDefs.BLAKE2b
  | BLAKE2s -> HashDefs.BLAKE2s
  | SHA1 -> HashDefs.Legacy HashDefs.SHA1
  | MD5 -> HashDefs.Legacy HashDefs.MD5
  | _ -> failwith "Algorithm not supported in agile Hashing API"


let output_len = function
  | SHA2_224
  | SHA3_224 -> 28
  | SHA2_256
  | SHA3_256
  | BLAKE2s -> 32
  | SHA2_384
  | SHA3_384 -> 48
  | SHA2_512
  | SHA3_512
  | BLAKE2b -> 64
  | Keccak_256 -> 32
  | SHA1 -> 20
  | MD5 -> 16


let test_agile (v: Bytes.t hash_test) =
  let test_result = test_result ("EverCrypt.Hash " ^ v.name)  in
  let alg = alg_definition v.alg in
  let digest = Test_utils.init_bytes (output_len v.alg) in

  Hash.Noalloc.hash ~alg ~msg:v.msg ~digest;
  let digest2 = Hash.hash ~alg ~msg:v.msg in
  if Bytes.equal digest v.expected &&
     Bytes.equal digest2 v.expected then
    test_result Success "one-shot hash"
  else
    test_result Failure "one-shot hash";

  let st = Hash.init ~alg:(alg_definition v.alg) in
  Hash.update ~st ~msg:v.msg;
  Hash.Noalloc.finish ~st ~digest;
  let digest2 = Hash.finish ~st in
  if Bytes.equal digest v.expected &&
     Bytes.equal digest2 v.expected then
    test_result Success "incremental hash"
  else
    test_result Failure "incremental hash"


let test_nonagile (n: string) (v: Bytes.t hash_test) hash hash_noalloc =
  let test_result = test_result (n ^ "." ^ v.name) in
  let digest = Test_utils.init_bytes (output_len v.alg) in
  hash_noalloc ~msg:v.msg ~digest;
  let digest2 = hash v.msg in
  if Bytes.equal digest v.expected &&
     Bytes.equal digest2 v.expected then
    test_result Success ""
  else
    test_result Failure ""


module MakeBlake2Tests (M: Blake2) = struct
  let test_nonagile_noalloc (v: Bytes.t blake2_keyed_test) t reqs =
    let test_result = test_result (t ^ " (noalloc) " ^ v.name) in
    if supports reqs then begin
      let output = Test_utils.init_bytes (Bytes.length v.expected) in
      M.Noalloc.hash ~key:v.key ~msg:v.msg ~digest:output;
      if Bytes.equal output v.expected then
        test_result Success ""
      else
        test_result Failure "Output mismatch"
    end else
      test_result Skipped "Required CPU feature not detected"

  let test_nonagile (v: Bytes.t blake2_keyed_test) t reqs =
    let test_result = test_result (t ^ " " ^ v.name) in
    if supports reqs then begin
      let size = Bytes.length v.expected in
      let digest = M.hash ~key:v.key v.msg size in
      if Bytes.equal digest v.expected then
        test_result Success ""
      else
        test_result Failure "Output mismatch"
    end else
      test_result Skipped "Required CPU feature not detected"

  let run_tests name tests reqs =
    List.iter (fun v -> test_nonagile_noalloc v name reqs) tests;
    List.iter (fun v -> test_nonagile v name reqs) tests
end


let test_keccak () =
  let v = test_sha3_256 in
  let test_result = test_result "Keccak/SHAKE" in
  let sha3_256 = Hacl.Keccak.keccak ~rate:1088 ~capacity:512 ~suffix:6 in
  let digest = sha3_256 ~msg:v.msg ~size:32 in

  let output_shake128 = Hacl.Keccak.shake128 ~msg:v.msg ~size:16 in

  let keccak_shake_128 = Hacl.Keccak.keccak ~rate:1344 ~capacity:256 ~suffix:31 in
  let output_keccak_shake_128 = keccak_shake_128 ~msg:v.msg ~size:16 in

  let output_shake256 = Hacl.Keccak.shake256 ~msg:v.msg ~size:32 in

  let keccak_shake_256 = Hacl.Keccak.keccak ~rate:1088 ~capacity:512 ~suffix:31 in
  let output_keccak_shake_256 = keccak_shake_256 ~msg:v.msg ~size:32 in

  let keccak_256 = Hacl.Keccak.keccak ~rate:1088 ~capacity:512 ~suffix:1 in
  let output_keccak_256 = keccak_256 ~msg:keccak256_test.msg ~size:32 in

  if Bytes.equal digest v.expected &&
     Bytes.equal output_shake128 output_keccak_shake_128 &&
     Bytes.equal output_shake256 output_keccak_shake_256 &&
     Bytes.equal output_keccak_256 keccak256_test.expected then
    test_result Success ""
  else
    test_result Failure ""


let test_keccak_noalloc () =
  let v = test_sha3_256 in
  let test_result = test_result "Keccak/SHAKE (noalloc)" in
  let sha3_256 = Hacl.Keccak.Noalloc.keccak ~rate:1088 ~capacity:512 ~suffix:6 in
  let digest = Test_utils.init_bytes 32 in
  sha3_256 ~msg:v.msg ~digest;

  let output_shake128 = Test_utils.init_bytes 16 in
  Hacl.Keccak.Noalloc.shake128 ~msg:v.msg ~digest:output_shake128;

  let keccak_shake_128 = Hacl.Keccak.Noalloc.keccak ~rate:1344 ~capacity:256 ~suffix:31 in
  let output_keccak_shake_128 = Test_utils.init_bytes 16 in
  keccak_shake_128 ~msg:v.msg ~digest:output_keccak_shake_128;

  let output_shake256 = Test_utils.init_bytes 32 in
  Hacl.Keccak.Noalloc.shake256 ~msg:v.msg ~digest:output_shake256;

  let keccak_shake_256 = Hacl.Keccak.Noalloc.keccak ~rate:1088 ~capacity:512 ~suffix:31 in
  let output_keccak_shake_256 = Test_utils.init_bytes 32 in
  keccak_shake_256 ~msg:v.msg ~digest:output_keccak_shake_256;

  let keccak_256 = Hacl.Keccak.Noalloc.keccak ~rate:1088 ~capacity:512 ~suffix:1 in
  let output_keccak_256 = Test_utils.init_bytes 32 in
  keccak_256 ~msg:keccak256_test.msg ~digest:output_keccak_256;

  if Bytes.equal digest v.expected &&
     Bytes.equal output_shake128 output_keccak_shake_128 &&
     Bytes.equal output_shake256 output_keccak_shake_256 &&
     Bytes.equal output_keccak_256 keccak256_test.expected then
    test_result Success ""
  else
    test_result Failure ""


let _ =
  test_agile test_sha2_224;
  test_agile test_sha2_256;
  test_agile test_sha2_384;
  test_agile test_sha2_512;
  test_agile test_blake2b;
  test_agile test_blake2s;

  test_nonagile "Hacl" test_sha2_224 Hacl.SHA2_224.hash Hacl.SHA2_224.Noalloc.hash;
  test_nonagile "Hacl" test_sha2_256 Hacl.SHA2_256.hash Hacl.SHA2_256.Noalloc.hash;
  test_nonagile "Hacl" test_sha2_384 Hacl.SHA2_384.hash Hacl.SHA2_384.Noalloc.hash;
  test_nonagile "Hacl" test_sha2_512 Hacl.SHA2_512.hash Hacl.SHA2_512.Noalloc.hash;

  test_nonagile "Hacl" test_sha3_224 Hacl.SHA3_224.hash Hacl.SHA3_224.Noalloc.hash;
  test_nonagile "Hacl" test_sha3_256 Hacl.SHA3_256.hash Hacl.SHA3_256.Noalloc.hash;
  test_nonagile "Hacl" test_sha3_384 Hacl.SHA3_384.hash Hacl.SHA3_384.Noalloc.hash;
  test_nonagile "Hacl" test_sha3_512 Hacl.SHA3_512.hash Hacl.SHA3_512.Noalloc.hash;

  test_nonagile "EverCrypt" test_sha2_224 EverCrypt.SHA2_224.hash EverCrypt.SHA2_224.Noalloc.hash;
  test_nonagile "EverCrypt" test_sha2_256 EverCrypt.SHA2_256.hash EverCrypt.SHA2_256.Noalloc.hash;

  test_agile test_sha1;
  test_agile test_md5;

  test_nonagile "Hacl" test_sha1 Hacl.SHA1.hash Hacl.SHA1.Noalloc.hash;
  test_nonagile "Hacl" test_md5 Hacl.MD5.hash Hacl.MD5.Noalloc.hash;

  let module Tests = MakeBlake2Tests (Hacl.Blake2b_32) in
  Tests.run_tests "BLAKE2b_32" blake2b_keyed_tests [];

  let module Tests = MakeBlake2Tests (Hacl.Blake2b_256) in
  Tests.run_tests "BLAKE2b_256" blake2b_keyed_tests [VEC256];

  let module Tests = MakeBlake2Tests (Hacl.Blake2s_32) in
  Tests.run_tests "BLAKE2s_32" blake2s_keyed_tests [];

  let module Tests = MakeBlake2Tests (Hacl.Blake2s_128) in
  Tests.run_tests "BLAKE2s_128" blake2s_keyed_tests [VEC128];

  test_keccak ();
  test_keccak_noalloc ()
