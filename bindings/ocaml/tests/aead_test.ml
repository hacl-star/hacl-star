open EverCrypt.Error
open AutoConfig2

open Test_utils

type 'a aead_test =
  { alg: EverCrypt.AEAD.alg;
    key_len: int; msg_len: int; iv_len: int ; ad_len: int; tag_len: int;
    test_key: 'a; test_iv: 'a; test_ad: 'a;
    test_pt: 'a; test_ct: 'a; test_tag: 'a
  }

(* TODO: add tests for AES128_GCM, AES256_GCM *)
let chacha20poly1305_test =
  { alg = EverCrypt.AEAD.CHACHA20_POLY1305; key_len = 32; msg_len = 114; iv_len = 12; ad_len = 12; tag_len = 16;
    test_key = Bytes.of_string "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f";
    test_iv = Bytes.of_string "\x07\x00\x00\x00\x40\x41\x42\x43\x44\x45\x46\x47";
    test_ad = Bytes.of_string "\x50\x51\x52\x53\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7";
    test_pt = Bytes.of_string "\x4c\x61\x64\x69\x65\x73\x20\x61\x6e\x64\x20\x47\x65\x6e\x74\x6c\x65\x6d\x65\x6e\x20\x6f\x66\x20\x74\x68\x65\x20\x63\x6c\x61\x73\x73\x20\x6f\x66\x20\x27\x39\x39\x3a\x20\x49\x66\x20\x49\x20\x63\x6f\x75\x6c\x64\x20\x6f\x66\x66\x65\x72\x20\x79\x6f\x75\x20\x6f\x6e\x6c\x79\x20\x6f\x6e\x65\x20\x74\x69\x70\x20\x66\x6f\x72\x20\x74\x68\x65\x20\x66\x75\x74\x75\x72\x65\x2c\x20\x73\x75\x6e\x73\x63\x72\x65\x65\x6e\x20\x77\x6f\x75\x6c\x64\x20\x62\x65\x20\x69\x74\x2e";
    test_ct = Bytes.of_string "\xd3\x1a\x8d\x34\x64\x8e\x60\xdb\x7b\x86\xaf\xbc\x53\xef\x7e\xc2\xa4\xad\xed\x51\x29\x6e\x08\xfe\xa9\xe2\xb5\xa7\x36\xee\x62\xd6\x3d\xbe\xa4\x5e\x8c\xa9\x67\x12\x82\xfa\xfb\x69\xda\x92\x72\x8b\x1a\x71\xde\x0a\x9e\x06\x0b\x29\x05\xd6\xa5\xb6\x7e\xcd\x3b\x36\x92\xdd\xbd\x7f\x2d\x77\x8b\x8c\x98\x03\xae\xe3\x28\x09\x1b\x58\xfa\xb3\x24\xe4\xfa\xd6\x75\x94\x55\x85\x80\x8b\x48\x31\xd7\xbc\x3f\xf4\xde\xf0\x8e\x4b\x7a\x9d\xe5\x76\xd2\x65\x86\xce\xc6\x4b\x61\x16";
    test_tag = Bytes.of_string "\x1a\xe1\x0b\x59\x4f\x09\xe2\x6a\x7e\x90\x2e\xcb\xd0\x60\x06\x91"
  }


let validate_test (v: Bytes.t aead_test) =
  assert (Bytes.length v.test_key = v.key_len);
  assert (Bytes.length v.test_iv = v.iv_len);
  assert (Bytes.length v.test_ad = v.ad_len);
  assert (Bytes.length v.test_pt = v.msg_len);
  assert (Bytes.length v.test_ct = v.msg_len);
  assert (Bytes.length v.test_tag = v.tag_len)

let test_agile (v: Bytes.t aead_test) =
  let open EverCrypt.AEAD in
  let test_result = test_result "EverCrypt.AEAD" in

  validate_test v;
  let ct = Test_utils.init_bytes v.msg_len in
  let tag = Test_utils.init_bytes v.tag_len in

  match init v.alg v.test_key with
  | Success st -> begin
      match encrypt st v.test_iv v.test_ad v.test_pt ct tag with
      | Success () -> begin
          if Bytes.compare tag v.test_tag = 0 && Bytes.compare ct v.test_ct = 0 then
            test_result Success "Encryption succeeded"
          else
            test_result Failure "Wrong ciphertext/mac";
          let dt = Test_utils.init_bytes v.msg_len in
          match decrypt st v.test_iv v.test_ad ct v.test_tag dt with
          | Success () ->
            if Bytes.compare v.test_pt dt = 0 then
              test_result Success "Decryption succeeded"
            else
              test_result Failure "Decrypted and plaintext do not match"
          | Error err -> test_result Failure (Printf.sprintf "Decryption error: %s" (print_error err))
        end
      | Error err -> test_result Failure (Printf.sprintf "Encryption error: %s" (print_error err))
    end
  | Error err -> test_result Failure (Printf.sprintf "Init error: %s" (print_error err))


let test_nonagile (v: Bytes.t aead_test) t encrypt decrypt reqs =
  let test_result = test_result t in

  if supports reqs then begin
    let ct = Test_utils.init_bytes v.msg_len in
    let tag = Test_utils.init_bytes v.tag_len in

    encrypt v.test_key v.test_iv v.test_ad v.test_pt ct tag;
    if Bytes.compare tag v.test_tag = 0 && Bytes.compare ct v.test_ct = 0 then
      test_result Success "Encryption succeeded"
    else
      test_result Failure
        (Printf.sprintf "Wrong ciphertext/mac %d %d \n" (Bytes.compare ct v.test_ct) (Bytes.compare tag v.test_tag));
    let dt = Test_utils.init_bytes v.msg_len in
    if decrypt v.test_key v.test_iv v.test_ad dt ct tag then
      if Bytes.compare v.test_pt dt = 0 then
        test_result Success "Decryption succeeded"
      else
        test_result Failure "Decrypted and plaintext do not match"
    else test_result Failure "Decryption error"
  end else
    test_result Skipped "Required CPU feature not detected"

let test_random () =
  let test_result = test_result "Lib.RandomBuffer" in
  let buf = Test_utils.init_bytes 256 in
  if Hacl.RandomBuffer.randombytes buf then
    test_result Success ""
  else
    test_result Failure ""

let _ =
  Printf.printf "SHAEXT: %b\n" (has_feature SHAEXT);
  Printf.printf "AES_NI: %b\n" (has_feature AES_NI);
  Printf.printf "PCLMULQDQ: %b\n" (has_feature PCLMULQDQ);
  Printf.printf "AVX2: %b\n" (has_feature AVX2);
  Printf.printf "AVX: %b\n" (has_feature AVX);
  Printf.printf "BMI2: %b\n" (has_feature BMI2);
  Printf.printf "ADX: %b\n" (has_feature ADX);
  Printf.printf "SSE: %b\n" (has_feature SSE);
  Printf.printf "MOVBE: %b\n" (has_feature MOVBE);
  Printf.printf "RDRAND: %b\n" (has_feature RDRAND);

  test_agile chacha20poly1305_test;
  test_nonagile chacha20poly1305_test "Hacl.Chacha20_Poly1305_32" Hacl.Chacha20_Poly1305_32.encrypt Hacl.Chacha20_Poly1305_32.decrypt [];
  test_nonagile chacha20poly1305_test "Hacl.Chacha20_Poly1305_128" Hacl.Chacha20_Poly1305_128.encrypt Hacl.Chacha20_Poly1305_128.decrypt [AVX];
  test_nonagile chacha20poly1305_test "Hacl.Chacha20_Poly1305_256" Hacl.Chacha20_Poly1305_256.encrypt Hacl.Chacha20_Poly1305_256.decrypt [AVX2];
  test_nonagile chacha20poly1305_test "EverCrypt.Chacha20_Poly1305_256" EverCrypt.Chacha20_Poly1305.encrypt EverCrypt.Chacha20_Poly1305.decrypt [];

  test_random ()
