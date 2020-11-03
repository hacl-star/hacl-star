module Spec.HPKE.Test

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module HPKE = Spec.Agile.HPKE
module DH = Spec.Agile.DH
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

friend Spec.Agile.HPKE

let print (str:string) =
  IO.print_string str

#set-options "--z3rlimit 100 --fuel 0 --ifuel 1"
let print_bytes (prefix:string) (len:size_nat) (bytes:lbytes len) =
  print prefix;
  List.iter (fun a -> print (UInt8.to_string (u8_to_UInt8 a))) (to_list bytes)

let compare_bytes (len:size_nat) (test_expected:lbytes len) (test_result:lbytes len) =
  for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test_expected test_result

let print_and_compare_bytes (len:size_nat) (test_expected:lbytes len) (test_result:lbytes len) =
  print_bytes "Result:   " len test_result;
  print "\n";
  print_bytes "Expected: " len test_expected;
  print "\n";
  compare_bytes len test_expected test_result

let print_and_compare_setup
  (cs:HPKE.ciphersuite)
  (enc:HPKE.key_dh_public_s cs)
  (key:HPKE.key_aead_s cs) (nonce:HPKE.nonce_aead_s cs) (exp_sec:HPKE.exporter_secret_s cs)
  (enc_i:HPKE.key_dh_public_s cs) (ctx_i:HPKE.encryption_context cs)
=
  let r1 = print_and_compare_bytes (HPKE.size_dh_public cs) enc enc_i in
  let r2 = print_and_compare_bytes (HPKE.size_aead_key cs) key (HPKE.key_of_ctx cs ctx_i) in
  let r3 = print_and_compare_bytes (HPKE.size_aead_nonce cs) nonce (HPKE.nonce_of_ctx cs ctx_i) in
  let r4 = print_and_compare_bytes (HPKE.size_kdf cs) exp_sec (HPKE.exp_sec_of_ctx cs ctx_i) in
  r1 && r2 && r3 && r4


let test_setupBase
  (cs:HPKE.ciphersuite)
  (skEm:HPKE.key_dh_secret_s cs) (pkEm:HPKE.key_dh_public_s cs) (skRm:HPKE.key_dh_secret_s cs) (pkRm:HPKE.key_dh_public_s cs) (info:HPKE.info_s cs)
  (enc:HPKE.key_dh_public_s cs) (zz:HPKE.key_kem_s cs)
  (ks_context:lbytes (HPKE.size_ks_ctx cs)) (secret:lbytes (HPKE.size_kdf cs))
  (key:HPKE.key_aead_s cs) (nonce:HPKE.nonce_aead_s cs) (exp_sec:HPKE.exporter_secret_s cs)
  (enc0_nonce:HPKE.nonce_aead_s cs) (enc1_nonce:HPKE.nonce_aead_s cs)
=
  print "Test setupBaseS\n";
  let pkR = HPKE.unmarshal cs pkRm in
  match HPKE.setupBaseS cs skEm pkR info with
  | None -> false
  | Some (enc_i, ctx_i) -> print_and_compare_setup cs enc key nonce exp_sec enc_i ctx_i

let test_export
  (cs:HPKE.ciphersuite)
  (key:HPKE.key_aead_s cs) (nonce:HPKE.nonce_aead_s cs) (exp_sec:HPKE.exporter_secret_s cs)
  (exp_ctx:HPKE.exp_ctx_s cs)
  (exp_len:size_nat{HKDF.expand_output_length_pred (HPKE.hash_of_cs cs) exp_len})
  (sec:lbytes exp_len)
=
  print "Test export\n";
  let ctx:(HPKE.encryption_context cs) = (key, nonce, 0, exp_sec) in
  let sec_i = HPKE.context_export cs ctx exp_ctx exp_len in
  let r = print_and_compare_bytes exp_len sec sec_i in
  r

let test_encryption
  (cs:HPKE.ciphersuite)
  (key:HPKE.key_aead_s cs) (nonce:HPKE.nonce_aead_s cs) (exp_sec:HPKE.exporter_secret_s cs)
  (aad:AEAD.ad (HPKE.aead_of_cs cs)) (pt:AEAD.plain (HPKE.aead_of_cs cs)) (seq:HPKE.seq_aead_s cs)
  (ct:AEAD.cipher (HPKE.aead_of_cs cs)) (enc_nonce:HPKE.nonce_aead_s cs)
=
  print "Test encryption\n";
  let ctx:(HPKE.encryption_context cs) = (key, nonce, seq, exp_sec) in
  let enc_nonce_i = HPKE.context_compute_nonce cs ctx seq in
  print_and_compare_bytes (HPKE.size_aead_nonce cs) enc_nonce enc_nonce_i


// Skipped unsupported test case 0

let test1_mode: HPKE.mode = HPKE.Base
let test1_ciphersuite = DH.DH_Curve25519, Hash.SHA2_256, AEAD.AES128_GCM, Hash.SHA2_256

// generated: "4f6465206f6e2061204772656369616e2055726e"
inline_for_extraction
let size_test1_info: size_nat = 20
let test1_info_list : l:list uint8{List.Tot.length l == size_test1_info} =
  [@inline_let]
  let l = [
    u8 0x4f; u8 0x64; u8 0x65; u8 0x20; u8 0x6f;
    u8 0x6e; u8 0x20; u8 0x61; u8 0x20; u8 0x47;
    u8 0x72; u8 0x65; u8 0x63; u8 0x69; u8 0x61;
    u8 0x6e; u8 0x20; u8 0x55; u8 0x72; u8 0x6e;
  ] in
  assert_norm(List.Tot.length l == size_test1_info);
  l
let test1_info : lbytes size_test1_info = createL test1_info_list

// generated: "919f0e1b7c361d1e5a3d0086ba94edeb6d2df9f756654741731f4e84cb813bdb"
inline_for_extraction
let size_test1_skRm: size_nat = 32
let test1_skRm_list : l:list uint8{List.Tot.length l == size_test1_skRm} =
  [@inline_let]
  let l = [
    u8 0x91; u8 0x9f; u8 0x0e; u8 0x1b; u8 0x7c;
    u8 0x36; u8 0x1d; u8 0x1e; u8 0x5a; u8 0x3d;
    u8 0x00; u8 0x86; u8 0xba; u8 0x94; u8 0xed;
    u8 0xeb; u8 0x6d; u8 0x2d; u8 0xf9; u8 0xf7;
    u8 0x56; u8 0x65; u8 0x47; u8 0x41; u8 0x73;
    u8 0x1f; u8 0x4e; u8 0x84; u8 0xcb; u8 0x81;
    u8 0x3b; u8 0xdb;
  ] in
  assert_norm(List.Tot.length l == size_test1_skRm);
  l
let test1_skRm : lbytes size_test1_skRm = createL test1_skRm_list

// generated: "232ce0da9fd45b8d500781a5ee1b0a2cf64411dd08d6442400ab05a4d29733a8"
inline_for_extraction
let size_test1_skEm: size_nat = 32
let test1_skEm_list : l:list uint8{List.Tot.length l == size_test1_skEm} =
  [@inline_let]
  let l = [
    u8 0x23; u8 0x2c; u8 0xe0; u8 0xda; u8 0x9f;
    u8 0xd4; u8 0x5b; u8 0x8d; u8 0x50; u8 0x07;
    u8 0x81; u8 0xa5; u8 0xee; u8 0x1b; u8 0x0a;
    u8 0x2c; u8 0xf6; u8 0x44; u8 0x11; u8 0xdd;
    u8 0x08; u8 0xd6; u8 0x44; u8 0x24; u8 0x00;
    u8 0xab; u8 0x05; u8 0xa4; u8 0xd2; u8 0x97;
    u8 0x33; u8 0xa8;
  ] in
  assert_norm(List.Tot.length l == size_test1_skEm);
  l
let test1_skEm : lbytes size_test1_skEm = createL test1_skEm_list

// generated: "ac511615dee12b2e11170f1272c3972e6e2268d8fb05fc93c6b008065f61f22f"
inline_for_extraction
let size_test1_pkRm: size_nat = 32
let test1_pkRm_list : l:list uint8{List.Tot.length l == size_test1_pkRm} =
  [@inline_let]
  let l = [
    u8 0xac; u8 0x51; u8 0x16; u8 0x15; u8 0xde;
    u8 0xe1; u8 0x2b; u8 0x2e; u8 0x11; u8 0x17;
    u8 0x0f; u8 0x12; u8 0x72; u8 0xc3; u8 0x97;
    u8 0x2e; u8 0x6e; u8 0x22; u8 0x68; u8 0xd8;
    u8 0xfb; u8 0x05; u8 0xfc; u8 0x93; u8 0xc6;
    u8 0xb0; u8 0x08; u8 0x06; u8 0x5f; u8 0x61;
    u8 0xf2; u8 0x2f;
  ] in
  assert_norm(List.Tot.length l == size_test1_pkRm);
  l
let test1_pkRm : lbytes size_test1_pkRm = createL test1_pkRm_list

// generated: "ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258"
inline_for_extraction
let size_test1_pkEm: size_nat = 32
let test1_pkEm_list : l:list uint8{List.Tot.length l == size_test1_pkEm} =
  [@inline_let]
  let l = [
    u8 0xab; u8 0x8b; u8 0x7f; u8 0xdd; u8 0xa7;
    u8 0xed; u8 0x10; u8 0xc4; u8 0x10; u8 0x07;
    u8 0x99; u8 0x09; u8 0x35; u8 0x09; u8 0x48;
    u8 0xff; u8 0x63; u8 0xbc; u8 0x04; u8 0x4b;
    u8 0x40; u8 0x57; u8 0x5c; u8 0xc8; u8 0x56;
    u8 0x36; u8 0xf3; u8 0x98; u8 0x1b; u8 0xb8;
    u8 0xd2; u8 0x58;
  ] in
  assert_norm(List.Tot.length l == size_test1_pkEm);
  l
let test1_pkEm : lbytes size_test1_pkEm = createL test1_pkEm_list

// generated: "ab8b7fdda7ed10c410079909350948ff63bc044b40575cc85636f3981bb8d258"
inline_for_extraction
let size_test1_enc: size_nat = 32
let test1_enc_list : l:list uint8{List.Tot.length l == size_test1_enc} =
  [@inline_let]
  let l = [
    u8 0xab; u8 0x8b; u8 0x7f; u8 0xdd; u8 0xa7;
    u8 0xed; u8 0x10; u8 0xc4; u8 0x10; u8 0x07;
    u8 0x99; u8 0x09; u8 0x35; u8 0x09; u8 0x48;
    u8 0xff; u8 0x63; u8 0xbc; u8 0x04; u8 0x4b;
    u8 0x40; u8 0x57; u8 0x5c; u8 0xc8; u8 0x56;
    u8 0x36; u8 0xf3; u8 0x98; u8 0x1b; u8 0xb8;
    u8 0xd2; u8 0x58;
  ] in
  assert_norm(List.Tot.length l == size_test1_enc);
  l
let test1_enc : lbytes size_test1_enc = createL test1_enc_list

// generated: "44807c99177b0f3761d66f422945a21317a1532ca038e976594487a6a7e58fbf"
inline_for_extraction
let size_test1_zz: size_nat = 32
let test1_zz_list : l:list uint8{List.Tot.length l == size_test1_zz} =
  [@inline_let]
  let l = [
    u8 0x44; u8 0x80; u8 0x7c; u8 0x99; u8 0x17;
    u8 0x7b; u8 0x0f; u8 0x37; u8 0x61; u8 0xd6;
    u8 0x6f; u8 0x42; u8 0x29; u8 0x45; u8 0xa2;
    u8 0x13; u8 0x17; u8 0xa1; u8 0x53; u8 0x2c;
    u8 0xa0; u8 0x38; u8 0xe9; u8 0x76; u8 0x59;
    u8 0x44; u8 0x87; u8 0xa6; u8 0xa7; u8 0xe5;
    u8 0x8f; u8 0xbf;
  ] in
  assert_norm(List.Tot.length l == size_test1_zz);
  l
let test1_zz : lbytes size_test1_zz = createL test1_zz_list

// generated: "002000010001005d0f5548cb13d7eba5320ae0e21b1ee274aac7ea1cce02570cf993d1b2456449debcca602075cf6f8ef506613a82e1c73727e2c912d0c49f16cd56fc524af4ce"
inline_for_extraction
let size_test1_key_schedule_context: size_nat = 71
let test1_key_schedule_context_list : l:list uint8{List.Tot.length l == size_test1_key_schedule_context} =
  [@inline_let]
  let l = [
    u8 0x00; u8 0x20; u8 0x00; u8 0x01; u8 0x00;
    u8 0x01; u8 0x00; u8 0x5d; u8 0x0f; u8 0x55;
    u8 0x48; u8 0xcb; u8 0x13; u8 0xd7; u8 0xeb;
    u8 0xa5; u8 0x32; u8 0x0a; u8 0xe0; u8 0xe2;
    u8 0x1b; u8 0x1e; u8 0xe2; u8 0x74; u8 0xaa;
    u8 0xc7; u8 0xea; u8 0x1c; u8 0xce; u8 0x02;
    u8 0x57; u8 0x0c; u8 0xf9; u8 0x93; u8 0xd1;
    u8 0xb2; u8 0x45; u8 0x64; u8 0x49; u8 0xde;
    u8 0xbc; u8 0xca; u8 0x60; u8 0x20; u8 0x75;
    u8 0xcf; u8 0x6f; u8 0x8e; u8 0xf5; u8 0x06;
    u8 0x61; u8 0x3a; u8 0x82; u8 0xe1; u8 0xc7;
    u8 0x37; u8 0x27; u8 0xe2; u8 0xc9; u8 0x12;
    u8 0xd0; u8 0xc4; u8 0x9f; u8 0x16; u8 0xcd;
    u8 0x56; u8 0xfc; u8 0x52; u8 0x4a; u8 0xf4;
    u8 0xce;
  ] in
  assert_norm(List.Tot.length l == size_test1_key_schedule_context);
  l
let test1_key_schedule_context : lbytes size_test1_key_schedule_context = createL test1_key_schedule_context_list

// generated: "c104521df56de97b517165011f09e0ea2a36b9af339a9de402c8b88547c8b67e"
inline_for_extraction
let size_test1_secret: size_nat = 32
let test1_secret_list : l:list uint8{List.Tot.length l == size_test1_secret} =
  [@inline_let]
  let l = [
    u8 0xc1; u8 0x04; u8 0x52; u8 0x1d; u8 0xf5;
    u8 0x6d; u8 0xe9; u8 0x7b; u8 0x51; u8 0x71;
    u8 0x65; u8 0x01; u8 0x1f; u8 0x09; u8 0xe0;
    u8 0xea; u8 0x2a; u8 0x36; u8 0xb9; u8 0xaf;
    u8 0x33; u8 0x9a; u8 0x9d; u8 0xe4; u8 0x02;
    u8 0xc8; u8 0xb8; u8 0x85; u8 0x47; u8 0xc8;
    u8 0xb6; u8 0x7e;
  ] in
  assert_norm(List.Tot.length l == size_test1_secret);
  l
let test1_secret : lbytes size_test1_secret = createL test1_secret_list

// generated: "e34afc8f8f4c2906b310d8e4e4d526f0"
inline_for_extraction
let size_test1_key: size_nat = 16
let test1_key_list : l:list uint8{List.Tot.length l == size_test1_key} =
  [@inline_let]
  let l = [
    u8 0xe3; u8 0x4a; u8 0xfc; u8 0x8f; u8 0x8f;
    u8 0x4c; u8 0x29; u8 0x06; u8 0xb3; u8 0x10;
    u8 0xd8; u8 0xe4; u8 0xe4; u8 0xd5; u8 0x26;
    u8 0xf0;
  ] in
  assert_norm(List.Tot.length l == size_test1_key);
  l
let test1_key : lbytes size_test1_key = createL test1_key_list

// generated: "2764228860619e140920c7d7"
inline_for_extraction
let size_test1_nonce: size_nat = 12
let test1_nonce_list : l:list uint8{List.Tot.length l == size_test1_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd7;
  ] in
  assert_norm(List.Tot.length l == size_test1_nonce);
  l
let test1_nonce : lbytes size_test1_nonce = createL test1_nonce_list

// generated: "93c6a28ec7af55f669612d5d64fe680ae38ca88d14fb6ecba647606eee668124"
inline_for_extraction
let size_test1_exporterSecret: size_nat = 32
let test1_exporterSecret_list : l:list uint8{List.Tot.length l == size_test1_exporterSecret} =
  [@inline_let]
  let l = [
    u8 0x93; u8 0xc6; u8 0xa2; u8 0x8e; u8 0xc7;
    u8 0xaf; u8 0x55; u8 0xf6; u8 0x69; u8 0x61;
    u8 0x2d; u8 0x5d; u8 0x64; u8 0xfe; u8 0x68;
    u8 0x0a; u8 0xe3; u8 0x8c; u8 0xa8; u8 0x8d;
    u8 0x14; u8 0xfb; u8 0x6e; u8 0xcb; u8 0xa6;
    u8 0x47; u8 0x60; u8 0x6e; u8 0xee; u8 0x66;
    u8 0x81; u8 0x24;
  ] in
  assert_norm(List.Tot.length l == size_test1_exporterSecret);
  l
let test1_exporterSecret : lbytes size_test1_exporterSecret = createL test1_exporterSecret_list

// generated: "436f756e742d30"
inline_for_extraction
let size_test1_encryption0_aad: size_nat = 7
let test1_encryption0_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption0_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x30;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption0_aad);
  l
let test1_encryption0_aad : lbytes size_test1_encryption0_aad = createL test1_encryption0_aad_list

// generated: "1811cf5d39f857f80175f96ca4d3600bfb0585e4ce119bc46396da4b371966a358924e5a97a7b53ea255971f6b"
inline_for_extraction
let size_test1_encryption0_ciphertext: size_nat = 45
let test1_encryption0_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption0_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x18; u8 0x11; u8 0xcf; u8 0x5d; u8 0x39;
    u8 0xf8; u8 0x57; u8 0xf8; u8 0x01; u8 0x75;
    u8 0xf9; u8 0x6c; u8 0xa4; u8 0xd3; u8 0x60;
    u8 0x0b; u8 0xfb; u8 0x05; u8 0x85; u8 0xe4;
    u8 0xce; u8 0x11; u8 0x9b; u8 0xc4; u8 0x63;
    u8 0x96; u8 0xda; u8 0x4b; u8 0x37; u8 0x19;
    u8 0x66; u8 0xa3; u8 0x58; u8 0x92; u8 0x4e;
    u8 0x5a; u8 0x97; u8 0xa7; u8 0xb5; u8 0x3e;
    u8 0xa2; u8 0x55; u8 0x97; u8 0x1f; u8 0x6b;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption0_ciphertext);
  l
let test1_encryption0_ciphertext : lbytes size_test1_encryption0_ciphertext = createL test1_encryption0_ciphertext_list

// generated: "2764228860619e140920c7d7"
inline_for_extraction
let size_test1_encryption0_nonce: size_nat = 12
let test1_encryption0_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption0_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd7;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption0_nonce);
  l
let test1_encryption0_nonce : lbytes size_test1_encryption0_nonce = createL test1_encryption0_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption0_plaintext: size_nat = 29
let test1_encryption0_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption0_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption0_plaintext);
  l
let test1_encryption0_plaintext : lbytes size_test1_encryption0_plaintext = createL test1_encryption0_plaintext_list

// generated: "436f756e742d31"
inline_for_extraction
let size_test1_encryption1_aad: size_nat = 7
let test1_encryption1_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption1_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x31;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption1_aad);
  l
let test1_encryption1_aad : lbytes size_test1_encryption1_aad = createL test1_encryption1_aad_list

// generated: "2ed9ff66c33bad2f7c0326881f05aa9616ccba13bdb126a0d2a5a3dfa6b95bd4de78a98ff64c1fb64b366074d4"
inline_for_extraction
let size_test1_encryption1_ciphertext: size_nat = 45
let test1_encryption1_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption1_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x2e; u8 0xd9; u8 0xff; u8 0x66; u8 0xc3;
    u8 0x3b; u8 0xad; u8 0x2f; u8 0x7c; u8 0x03;
    u8 0x26; u8 0x88; u8 0x1f; u8 0x05; u8 0xaa;
    u8 0x96; u8 0x16; u8 0xcc; u8 0xba; u8 0x13;
    u8 0xbd; u8 0xb1; u8 0x26; u8 0xa0; u8 0xd2;
    u8 0xa5; u8 0xa3; u8 0xdf; u8 0xa6; u8 0xb9;
    u8 0x5b; u8 0xd4; u8 0xde; u8 0x78; u8 0xa9;
    u8 0x8f; u8 0xf6; u8 0x4c; u8 0x1f; u8 0xb6;
    u8 0x4b; u8 0x36; u8 0x60; u8 0x74; u8 0xd4;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption1_ciphertext);
  l
let test1_encryption1_ciphertext : lbytes size_test1_encryption1_ciphertext = createL test1_encryption1_ciphertext_list

// generated: "2764228860619e140920c7d6"
inline_for_extraction
let size_test1_encryption1_nonce: size_nat = 12
let test1_encryption1_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption1_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd6;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption1_nonce);
  l
let test1_encryption1_nonce : lbytes size_test1_encryption1_nonce = createL test1_encryption1_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption1_plaintext: size_nat = 29
let test1_encryption1_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption1_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption1_plaintext);
  l
let test1_encryption1_plaintext : lbytes size_test1_encryption1_plaintext = createL test1_encryption1_plaintext_list

// generated: "436f756e742d32"
inline_for_extraction
let size_test1_encryption2_aad: size_nat = 7
let test1_encryption2_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption2_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x32;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption2_aad);
  l
let test1_encryption2_aad : lbytes size_test1_encryption2_aad = createL test1_encryption2_aad_list

// generated: "4bfc8da6f1da808be2c1c141e864fe536bd1e9c4e01376cd383370b8095438a06f372e663739b30af9355da8a3"
inline_for_extraction
let size_test1_encryption2_ciphertext: size_nat = 45
let test1_encryption2_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption2_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x4b; u8 0xfc; u8 0x8d; u8 0xa6; u8 0xf1;
    u8 0xda; u8 0x80; u8 0x8b; u8 0xe2; u8 0xc1;
    u8 0xc1; u8 0x41; u8 0xe8; u8 0x64; u8 0xfe;
    u8 0x53; u8 0x6b; u8 0xd1; u8 0xe9; u8 0xc4;
    u8 0xe0; u8 0x13; u8 0x76; u8 0xcd; u8 0x38;
    u8 0x33; u8 0x70; u8 0xb8; u8 0x09; u8 0x54;
    u8 0x38; u8 0xa0; u8 0x6f; u8 0x37; u8 0x2e;
    u8 0x66; u8 0x37; u8 0x39; u8 0xb3; u8 0x0a;
    u8 0xf9; u8 0x35; u8 0x5d; u8 0xa8; u8 0xa3;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption2_ciphertext);
  l
let test1_encryption2_ciphertext : lbytes size_test1_encryption2_ciphertext = createL test1_encryption2_ciphertext_list

// generated: "2764228860619e140920c7d5"
inline_for_extraction
let size_test1_encryption2_nonce: size_nat = 12
let test1_encryption2_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption2_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd5;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption2_nonce);
  l
let test1_encryption2_nonce : lbytes size_test1_encryption2_nonce = createL test1_encryption2_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption2_plaintext: size_nat = 29
let test1_encryption2_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption2_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption2_plaintext);
  l
let test1_encryption2_plaintext : lbytes size_test1_encryption2_plaintext = createL test1_encryption2_plaintext_list

// generated: "436f756e742d33"
inline_for_extraction
let size_test1_encryption3_aad: size_nat = 7
let test1_encryption3_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption3_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x33;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption3_aad);
  l
let test1_encryption3_aad : lbytes size_test1_encryption3_aad = createL test1_encryption3_aad_list

// generated: "cc82487c2beb92d6810a40bad2aa96794c5f2b6eff96a674cf9c9c853397e6c7ca9640c200a38326adb63ed7f2"
inline_for_extraction
let size_test1_encryption3_ciphertext: size_nat = 45
let test1_encryption3_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption3_ciphertext} =
  [@inline_let]
  let l = [
    u8 0xcc; u8 0x82; u8 0x48; u8 0x7c; u8 0x2b;
    u8 0xeb; u8 0x92; u8 0xd6; u8 0x81; u8 0x0a;
    u8 0x40; u8 0xba; u8 0xd2; u8 0xaa; u8 0x96;
    u8 0x79; u8 0x4c; u8 0x5f; u8 0x2b; u8 0x6e;
    u8 0xff; u8 0x96; u8 0xa6; u8 0x74; u8 0xcf;
    u8 0x9c; u8 0x9c; u8 0x85; u8 0x33; u8 0x97;
    u8 0xe6; u8 0xc7; u8 0xca; u8 0x96; u8 0x40;
    u8 0xc2; u8 0x00; u8 0xa3; u8 0x83; u8 0x26;
    u8 0xad; u8 0xb6; u8 0x3e; u8 0xd7; u8 0xf2;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption3_ciphertext);
  l
let test1_encryption3_ciphertext : lbytes size_test1_encryption3_ciphertext = createL test1_encryption3_ciphertext_list

// generated: "2764228860619e140920c7d4"
inline_for_extraction
let size_test1_encryption3_nonce: size_nat = 12
let test1_encryption3_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption3_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd4;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption3_nonce);
  l
let test1_encryption3_nonce : lbytes size_test1_encryption3_nonce = createL test1_encryption3_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption3_plaintext: size_nat = 29
let test1_encryption3_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption3_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption3_plaintext);
  l
let test1_encryption3_plaintext : lbytes size_test1_encryption3_plaintext = createL test1_encryption3_plaintext_list

// generated: "436f756e742d34"
inline_for_extraction
let size_test1_encryption4_aad: size_nat = 7
let test1_encryption4_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption4_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x34;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption4_aad);
  l
let test1_encryption4_aad : lbytes size_test1_encryption4_aad = createL test1_encryption4_aad_list

// generated: "6314e60548cfdc30552303be4cb19875e335554bce186e1b41f9d15b4b4a4af77d68c09ebf883a9cbb51f3be9d"
inline_for_extraction
let size_test1_encryption4_ciphertext: size_nat = 45
let test1_encryption4_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption4_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x63; u8 0x14; u8 0xe6; u8 0x05; u8 0x48;
    u8 0xcf; u8 0xdc; u8 0x30; u8 0x55; u8 0x23;
    u8 0x03; u8 0xbe; u8 0x4c; u8 0xb1; u8 0x98;
    u8 0x75; u8 0xe3; u8 0x35; u8 0x55; u8 0x4b;
    u8 0xce; u8 0x18; u8 0x6e; u8 0x1b; u8 0x41;
    u8 0xf9; u8 0xd1; u8 0x5b; u8 0x4b; u8 0x4a;
    u8 0x4a; u8 0xf7; u8 0x7d; u8 0x68; u8 0xc0;
    u8 0x9e; u8 0xbf; u8 0x88; u8 0x3a; u8 0x9c;
    u8 0xbb; u8 0x51; u8 0xf3; u8 0xbe; u8 0x9d;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption4_ciphertext);
  l
let test1_encryption4_ciphertext : lbytes size_test1_encryption4_ciphertext = createL test1_encryption4_ciphertext_list

// generated: "2764228860619e140920c7d3"
inline_for_extraction
let size_test1_encryption4_nonce: size_nat = 12
let test1_encryption4_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption4_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd3;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption4_nonce);
  l
let test1_encryption4_nonce : lbytes size_test1_encryption4_nonce = createL test1_encryption4_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption4_plaintext: size_nat = 29
let test1_encryption4_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption4_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption4_plaintext);
  l
let test1_encryption4_plaintext : lbytes size_test1_encryption4_plaintext = createL test1_encryption4_plaintext_list

// generated: "436f756e742d35"
inline_for_extraction
let size_test1_encryption5_aad: size_nat = 7
let test1_encryption5_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption5_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x35;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption5_aad);
  l
let test1_encryption5_aad : lbytes size_test1_encryption5_aad = createL test1_encryption5_aad_list

// generated: "ce580d139c001ed794c4eedf14ce43c19c2a04f20dcfa9de57b6f555816b0558db4ec603bbc3748dce30e5c82f"
inline_for_extraction
let size_test1_encryption5_ciphertext: size_nat = 45
let test1_encryption5_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption5_ciphertext} =
  [@inline_let]
  let l = [
    u8 0xce; u8 0x58; u8 0x0d; u8 0x13; u8 0x9c;
    u8 0x00; u8 0x1e; u8 0xd7; u8 0x94; u8 0xc4;
    u8 0xee; u8 0xdf; u8 0x14; u8 0xce; u8 0x43;
    u8 0xc1; u8 0x9c; u8 0x2a; u8 0x04; u8 0xf2;
    u8 0x0d; u8 0xcf; u8 0xa9; u8 0xde; u8 0x57;
    u8 0xb6; u8 0xf5; u8 0x55; u8 0x81; u8 0x6b;
    u8 0x05; u8 0x58; u8 0xdb; u8 0x4e; u8 0xc6;
    u8 0x03; u8 0xbb; u8 0xc3; u8 0x74; u8 0x8d;
    u8 0xce; u8 0x30; u8 0xe5; u8 0xc8; u8 0x2f;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption5_ciphertext);
  l
let test1_encryption5_ciphertext : lbytes size_test1_encryption5_ciphertext = createL test1_encryption5_ciphertext_list

// generated: "2764228860619e140920c7d2"
inline_for_extraction
let size_test1_encryption5_nonce: size_nat = 12
let test1_encryption5_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption5_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd2;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption5_nonce);
  l
let test1_encryption5_nonce : lbytes size_test1_encryption5_nonce = createL test1_encryption5_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption5_plaintext: size_nat = 29
let test1_encryption5_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption5_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption5_plaintext);
  l
let test1_encryption5_plaintext : lbytes size_test1_encryption5_plaintext = createL test1_encryption5_plaintext_list

// generated: "436f756e742d36"
inline_for_extraction
let size_test1_encryption6_aad: size_nat = 7
let test1_encryption6_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption6_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x36;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption6_aad);
  l
let test1_encryption6_aad : lbytes size_test1_encryption6_aad = createL test1_encryption6_aad_list

// generated: "5247db08759b2a6d9459a4cc461dfc59afb78e37b0852f9a669720df72fe5781460bcc9ae5ca00545ad06f93c3"
inline_for_extraction
let size_test1_encryption6_ciphertext: size_nat = 45
let test1_encryption6_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption6_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x52; u8 0x47; u8 0xdb; u8 0x08; u8 0x75;
    u8 0x9b; u8 0x2a; u8 0x6d; u8 0x94; u8 0x59;
    u8 0xa4; u8 0xcc; u8 0x46; u8 0x1d; u8 0xfc;
    u8 0x59; u8 0xaf; u8 0xb7; u8 0x8e; u8 0x37;
    u8 0xb0; u8 0x85; u8 0x2f; u8 0x9a; u8 0x66;
    u8 0x97; u8 0x20; u8 0xdf; u8 0x72; u8 0xfe;
    u8 0x57; u8 0x81; u8 0x46; u8 0x0b; u8 0xcc;
    u8 0x9a; u8 0xe5; u8 0xca; u8 0x00; u8 0x54;
    u8 0x5a; u8 0xd0; u8 0x6f; u8 0x93; u8 0xc3;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption6_ciphertext);
  l
let test1_encryption6_ciphertext : lbytes size_test1_encryption6_ciphertext = createL test1_encryption6_ciphertext_list

// generated: "2764228860619e140920c7d1"
inline_for_extraction
let size_test1_encryption6_nonce: size_nat = 12
let test1_encryption6_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption6_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd1;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption6_nonce);
  l
let test1_encryption6_nonce : lbytes size_test1_encryption6_nonce = createL test1_encryption6_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption6_plaintext: size_nat = 29
let test1_encryption6_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption6_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption6_plaintext);
  l
let test1_encryption6_plaintext : lbytes size_test1_encryption6_plaintext = createL test1_encryption6_plaintext_list

// generated: "436f756e742d37"
inline_for_extraction
let size_test1_encryption7_aad: size_nat = 7
let test1_encryption7_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption7_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x37;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption7_aad);
  l
let test1_encryption7_aad : lbytes size_test1_encryption7_aad = createL test1_encryption7_aad_list

// generated: "e4ac909e74ca97d420374dba157678aad8f335b5cdaac2ca2e1813f2b3a6c0f6cfbc690dfd9b04a140861b910b"
inline_for_extraction
let size_test1_encryption7_ciphertext: size_nat = 45
let test1_encryption7_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption7_ciphertext} =
  [@inline_let]
  let l = [
    u8 0xe4; u8 0xac; u8 0x90; u8 0x9e; u8 0x74;
    u8 0xca; u8 0x97; u8 0xd4; u8 0x20; u8 0x37;
    u8 0x4d; u8 0xba; u8 0x15; u8 0x76; u8 0x78;
    u8 0xaa; u8 0xd8; u8 0xf3; u8 0x35; u8 0xb5;
    u8 0xcd; u8 0xaa; u8 0xc2; u8 0xca; u8 0x2e;
    u8 0x18; u8 0x13; u8 0xf2; u8 0xb3; u8 0xa6;
    u8 0xc0; u8 0xf6; u8 0xcf; u8 0xbc; u8 0x69;
    u8 0x0d; u8 0xfd; u8 0x9b; u8 0x04; u8 0xa1;
    u8 0x40; u8 0x86; u8 0x1b; u8 0x91; u8 0x0b;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption7_ciphertext);
  l
let test1_encryption7_ciphertext : lbytes size_test1_encryption7_ciphertext = createL test1_encryption7_ciphertext_list

// generated: "2764228860619e140920c7d0"
inline_for_extraction
let size_test1_encryption7_nonce: size_nat = 12
let test1_encryption7_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption7_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xd0;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption7_nonce);
  l
let test1_encryption7_nonce : lbytes size_test1_encryption7_nonce = createL test1_encryption7_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption7_plaintext: size_nat = 29
let test1_encryption7_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption7_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption7_plaintext);
  l
let test1_encryption7_plaintext : lbytes size_test1_encryption7_plaintext = createL test1_encryption7_plaintext_list

// generated: "436f756e742d38"
inline_for_extraction
let size_test1_encryption8_aad: size_nat = 7
let test1_encryption8_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption8_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x38;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption8_aad);
  l
let test1_encryption8_aad : lbytes size_test1_encryption8_aad = createL test1_encryption8_aad_list

// generated: "bd664ef7fa8fd4ba23430453914ffa75c54c24a593d894ad6626635ef38792cf505b7925d2f8dcdc744b8a8acd"
inline_for_extraction
let size_test1_encryption8_ciphertext: size_nat = 45
let test1_encryption8_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption8_ciphertext} =
  [@inline_let]
  let l = [
    u8 0xbd; u8 0x66; u8 0x4e; u8 0xf7; u8 0xfa;
    u8 0x8f; u8 0xd4; u8 0xba; u8 0x23; u8 0x43;
    u8 0x04; u8 0x53; u8 0x91; u8 0x4f; u8 0xfa;
    u8 0x75; u8 0xc5; u8 0x4c; u8 0x24; u8 0xa5;
    u8 0x93; u8 0xd8; u8 0x94; u8 0xad; u8 0x66;
    u8 0x26; u8 0x63; u8 0x5e; u8 0xf3; u8 0x87;
    u8 0x92; u8 0xcf; u8 0x50; u8 0x5b; u8 0x79;
    u8 0x25; u8 0xd2; u8 0xf8; u8 0xdc; u8 0xdc;
    u8 0x74; u8 0x4b; u8 0x8a; u8 0x8a; u8 0xcd;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption8_ciphertext);
  l
let test1_encryption8_ciphertext : lbytes size_test1_encryption8_ciphertext = createL test1_encryption8_ciphertext_list

// generated: "2764228860619e140920c7df"
inline_for_extraction
let size_test1_encryption8_nonce: size_nat = 12
let test1_encryption8_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption8_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xdf;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption8_nonce);
  l
let test1_encryption8_nonce : lbytes size_test1_encryption8_nonce = createL test1_encryption8_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption8_plaintext: size_nat = 29
let test1_encryption8_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption8_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption8_plaintext);
  l
let test1_encryption8_plaintext : lbytes size_test1_encryption8_plaintext = createL test1_encryption8_plaintext_list

// generated: "436f756e742d39"
inline_for_extraction
let size_test1_encryption9_aad: size_nat = 7
let test1_encryption9_aad_list : l:list uint8{List.Tot.length l == size_test1_encryption9_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x39;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption9_aad);
  l
let test1_encryption9_aad : lbytes size_test1_encryption9_aad = createL test1_encryption9_aad_list

// generated: "4b7f4832efecd0a808a367e4d2ac970d6604026e4386211c22912567a061a2558de77f7cb760f1837f6d048d71"
inline_for_extraction
let size_test1_encryption9_ciphertext: size_nat = 45
let test1_encryption9_ciphertext_list : l:list uint8{List.Tot.length l == size_test1_encryption9_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x4b; u8 0x7f; u8 0x48; u8 0x32; u8 0xef;
    u8 0xec; u8 0xd0; u8 0xa8; u8 0x08; u8 0xa3;
    u8 0x67; u8 0xe4; u8 0xd2; u8 0xac; u8 0x97;
    u8 0x0d; u8 0x66; u8 0x04; u8 0x02; u8 0x6e;
    u8 0x43; u8 0x86; u8 0x21; u8 0x1c; u8 0x22;
    u8 0x91; u8 0x25; u8 0x67; u8 0xa0; u8 0x61;
    u8 0xa2; u8 0x55; u8 0x8d; u8 0xe7; u8 0x7f;
    u8 0x7c; u8 0xb7; u8 0x60; u8 0xf1; u8 0x83;
    u8 0x7f; u8 0x6d; u8 0x04; u8 0x8d; u8 0x71;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption9_ciphertext);
  l
let test1_encryption9_ciphertext : lbytes size_test1_encryption9_ciphertext = createL test1_encryption9_ciphertext_list

// generated: "2764228860619e140920c7de"
inline_for_extraction
let size_test1_encryption9_nonce: size_nat = 12
let test1_encryption9_nonce_list : l:list uint8{List.Tot.length l == size_test1_encryption9_nonce} =
  [@inline_let]
  let l = [
    u8 0x27; u8 0x64; u8 0x22; u8 0x88; u8 0x60;
    u8 0x61; u8 0x9e; u8 0x14; u8 0x09; u8 0x20;
    u8 0xc7; u8 0xde;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption9_nonce);
  l
let test1_encryption9_nonce : lbytes size_test1_encryption9_nonce = createL test1_encryption9_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test1_encryption9_plaintext: size_nat = 29
let test1_encryption9_plaintext_list : l:list uint8{List.Tot.length l == size_test1_encryption9_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test1_encryption9_plaintext);
  l
let test1_encryption9_plaintext : lbytes size_test1_encryption9_plaintext = createL test1_encryption9_plaintext_list

// generated: "436f6e746578742d30"
inline_for_extraction
let size_test1_export0_exportContext: size_nat = 9
let test1_export0_exportContext_list : l:list uint8{List.Tot.length l == size_test1_export0_exportContext} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x6e; u8 0x74; u8 0x65;
    u8 0x78; u8 0x74; u8 0x2d; u8 0x30;
  ] in
  assert_norm(List.Tot.length l == size_test1_export0_exportContext);
  l
let test1_export0_exportContext : lbytes size_test1_export0_exportContext = createL test1_export0_exportContext_list

// generated: "76d8f9425846916bf678504e398e984d91878220f34c5a5e1a63ac75ba0176bc"
inline_for_extraction
let size_test1_export0_exportValue: size_nat = 32
let test1_export0_exportValue_list : l:list uint8{List.Tot.length l == size_test1_export0_exportValue} =
  [@inline_let]
  let l = [
    u8 0x76; u8 0xd8; u8 0xf9; u8 0x42; u8 0x58;
    u8 0x46; u8 0x91; u8 0x6b; u8 0xf6; u8 0x78;
    u8 0x50; u8 0x4e; u8 0x39; u8 0x8e; u8 0x98;
    u8 0x4d; u8 0x91; u8 0x87; u8 0x82; u8 0x20;
    u8 0xf3; u8 0x4c; u8 0x5a; u8 0x5e; u8 0x1a;
    u8 0x63; u8 0xac; u8 0x75; u8 0xba; u8 0x01;
    u8 0x76; u8 0xbc;
  ] in
  assert_norm(List.Tot.length l == size_test1_export0_exportValue);
  l
let test1_export0_exportValue : lbytes size_test1_export0_exportValue = createL test1_export0_exportValue_list

let test1_export0_len:size_nat = 32
// generated: "436f6e746578742d31"
inline_for_extraction
let size_test1_export1_exportContext: size_nat = 9
let test1_export1_exportContext_list : l:list uint8{List.Tot.length l == size_test1_export1_exportContext} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x6e; u8 0x74; u8 0x65;
    u8 0x78; u8 0x74; u8 0x2d; u8 0x31;
  ] in
  assert_norm(List.Tot.length l == size_test1_export1_exportContext);
  l
let test1_export1_exportContext : lbytes size_test1_export1_exportContext = createL test1_export1_exportContext_list

// generated: "94fe3245047dde534862778ca1962e594b1758df5a525b4caa54ff0feadad06b"
inline_for_extraction
let size_test1_export1_exportValue: size_nat = 32
let test1_export1_exportValue_list : l:list uint8{List.Tot.length l == size_test1_export1_exportValue} =
  [@inline_let]
  let l = [
    u8 0x94; u8 0xfe; u8 0x32; u8 0x45; u8 0x04;
    u8 0x7d; u8 0xde; u8 0x53; u8 0x48; u8 0x62;
    u8 0x77; u8 0x8c; u8 0xa1; u8 0x96; u8 0x2e;
    u8 0x59; u8 0x4b; u8 0x17; u8 0x58; u8 0xdf;
    u8 0x5a; u8 0x52; u8 0x5b; u8 0x4c; u8 0xaa;
    u8 0x54; u8 0xff; u8 0x0f; u8 0xea; u8 0xda;
    u8 0xd0; u8 0x6b;
  ] in
  assert_norm(List.Tot.length l == size_test1_export1_exportValue);
  l
let test1_export1_exportValue : lbytes size_test1_export1_exportValue = createL test1_export1_exportValue_list

let test1_export1_len:size_nat = 32
// generated: "436f6e746578742d32"
inline_for_extraction
let size_test1_export2_exportContext: size_nat = 9
let test1_export2_exportContext_list : l:list uint8{List.Tot.length l == size_test1_export2_exportContext} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x6e; u8 0x74; u8 0x65;
    u8 0x78; u8 0x74; u8 0x2d; u8 0x32;
  ] in
  assert_norm(List.Tot.length l == size_test1_export2_exportContext);
  l
let test1_export2_exportContext : lbytes size_test1_export2_exportContext = createL test1_export2_exportContext_list

// generated: "97f0c64128ff1379af9ec623cba204b50cd9db9a6b7d90e7a28fed06badf363e"
inline_for_extraction
let size_test1_export2_exportValue: size_nat = 32
let test1_export2_exportValue_list : l:list uint8{List.Tot.length l == size_test1_export2_exportValue} =
  [@inline_let]
  let l = [
    u8 0x97; u8 0xf0; u8 0xc6; u8 0x41; u8 0x28;
    u8 0xff; u8 0x13; u8 0x79; u8 0xaf; u8 0x9e;
    u8 0xc6; u8 0x23; u8 0xcb; u8 0xa2; u8 0x04;
    u8 0xb5; u8 0x0c; u8 0xd9; u8 0xdb; u8 0x9a;
    u8 0x6b; u8 0x7d; u8 0x90; u8 0xe7; u8 0xa2;
    u8 0x8f; u8 0xed; u8 0x06; u8 0xba; u8 0xdf;
    u8 0x36; u8 0x3e;
  ] in
  assert_norm(List.Tot.length l == size_test1_export2_exportValue);
  l
let test1_export2_exportValue : lbytes size_test1_export2_exportValue = createL test1_export2_exportValue_list

let test1_export2_len:size_nat = 32
// generated: "436f6e746578742d33"
inline_for_extraction
let size_test1_export3_exportContext: size_nat = 9
let test1_export3_exportContext_list : l:list uint8{List.Tot.length l == size_test1_export3_exportContext} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x6e; u8 0x74; u8 0x65;
    u8 0x78; u8 0x74; u8 0x2d; u8 0x33;
  ] in
  assert_norm(List.Tot.length l == size_test1_export3_exportContext);
  l
let test1_export3_exportContext : lbytes size_test1_export3_exportContext = createL test1_export3_exportContext_list

// generated: "9cd27f832e7271f82ae85c3404d7d06ab2a5bebb9354bc022b9f016d74bcdb2c"
inline_for_extraction
let size_test1_export3_exportValue: size_nat = 32
let test1_export3_exportValue_list : l:list uint8{List.Tot.length l == size_test1_export3_exportValue} =
  [@inline_let]
  let l = [
    u8 0x9c; u8 0xd2; u8 0x7f; u8 0x83; u8 0x2e;
    u8 0x72; u8 0x71; u8 0xf8; u8 0x2a; u8 0xe8;
    u8 0x5c; u8 0x34; u8 0x04; u8 0xd7; u8 0xd0;
    u8 0x6a; u8 0xb2; u8 0xa5; u8 0xbe; u8 0xbb;
    u8 0x93; u8 0x54; u8 0xbc; u8 0x02; u8 0x2b;
    u8 0x9f; u8 0x01; u8 0x6d; u8 0x74; u8 0xbc;
    u8 0xdb; u8 0x2c;
  ] in
  assert_norm(List.Tot.length l == size_test1_export3_exportValue);
  l
let test1_export3_exportValue : lbytes size_test1_export3_exportValue = createL test1_export3_exportValue_list

let test1_export3_len:size_nat = 32
// generated: "436f6e746578742d34"
inline_for_extraction
let size_test1_export4_exportContext: size_nat = 9
let test1_export4_exportContext_list : l:list uint8{List.Tot.length l == size_test1_export4_exportContext} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x6e; u8 0x74; u8 0x65;
    u8 0x78; u8 0x74; u8 0x2d; u8 0x34;
  ] in
  assert_norm(List.Tot.length l == size_test1_export4_exportContext);
  l
let test1_export4_exportContext : lbytes size_test1_export4_exportContext = createL test1_export4_exportContext_list

// generated: "74da0b06441dd2aca2a43d5ee4796158c9403f7037e93c50bcbd6ea4a1687c06"
inline_for_extraction
let size_test1_export4_exportValue: size_nat = 32
let test1_export4_exportValue_list : l:list uint8{List.Tot.length l == size_test1_export4_exportValue} =
  [@inline_let]
  let l = [
    u8 0x74; u8 0xda; u8 0x0b; u8 0x06; u8 0x44;
    u8 0x1d; u8 0xd2; u8 0xac; u8 0xa2; u8 0xa4;
    u8 0x3d; u8 0x5e; u8 0xe4; u8 0x79; u8 0x61;
    u8 0x58; u8 0xc9; u8 0x40; u8 0x3f; u8 0x70;
    u8 0x37; u8 0xe9; u8 0x3c; u8 0x50; u8 0xbc;
    u8 0xbd; u8 0x6e; u8 0xa4; u8 0xa1; u8 0x68;
    u8 0x7c; u8 0x06;
  ] in
  assert_norm(List.Tot.length l == size_test1_export4_exportValue);
  l
let test1_export4_exportValue : lbytes size_test1_export4_exportValue = createL test1_export4_exportValue_list

let test1_export4_len:size_nat = 32

let test1 () =
  let res = test_setupBase test1_ciphersuite test1_skEm test1_pkEm test1_skRm test1_pkRm test1_info test1_enc test1_zz test1_key_schedule_context test1_secret test1_key test1_nonce test1_exporterSecret test1_encryption0_nonce test1_encryption1_nonce in
  let seq0:HPKE.seq_aead_s test1_ciphersuite = 0 in
  let enc_res0 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption0_aad test1_encryption0_plaintext seq0 test1_encryption0_ciphertext test1_encryption0_nonce in

  assert_norm (1 < pow2 (8 * 12));
  let seq1:HPKE.seq_aead_s test1_ciphersuite = (seq0 + 1) in
  let enc_res1 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption1_aad test1_encryption1_plaintext seq1 test1_encryption1_ciphertext test1_encryption1_nonce in

  assert_norm (2 < pow2 (8 * 12));
  let seq2:HPKE.seq_aead_s test1_ciphersuite = (seq1 + 1) in
  let enc_res2 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption2_aad test1_encryption2_plaintext 2 test1_encryption2_ciphertext test1_encryption2_nonce in

  assert_norm (3 < pow2 (8 * 12));
  let seq3:HPKE.seq_aead_s test1_ciphersuite = (seq2 + 1) in
  let enc_res3 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption3_aad test1_encryption3_plaintext 3 test1_encryption3_ciphertext test1_encryption3_nonce in

  assert_norm (4 < pow2 (8 * 12));
  let seq4:HPKE.seq_aead_s test1_ciphersuite = (seq3 + 1) in
  let enc_res4 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption4_aad test1_encryption4_plaintext 4 test1_encryption4_ciphertext test1_encryption4_nonce in

  assert_norm (5 < pow2 (8 * 12));
  let seq5:HPKE.seq_aead_s test1_ciphersuite = (seq4 + 1) in
  let enc_res5 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption5_aad test1_encryption5_plaintext 5 test1_encryption5_ciphertext test1_encryption5_nonce in

  assert_norm (6 < pow2 (8 * 12));
  let seq6:HPKE.seq_aead_s test1_ciphersuite = (seq5 + 1) in
  let enc_res6 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption6_aad test1_encryption6_plaintext 6 test1_encryption6_ciphertext test1_encryption6_nonce in

  assert_norm (7 < pow2 (8 * 12));
  let seq7:HPKE.seq_aead_s test1_ciphersuite = (seq6 + 1) in
  let enc_res7 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption7_aad test1_encryption7_plaintext 7 test1_encryption7_ciphertext test1_encryption7_nonce in

  assert_norm (8 < pow2 (8 * 12));
  let seq8:HPKE.seq_aead_s test1_ciphersuite = (seq7 + 1) in
  let enc_res8 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption8_aad test1_encryption8_plaintext 8 test1_encryption8_ciphertext test1_encryption8_nonce in

  assert_norm (9 < pow2 (8 * 12));
  let seq9:HPKE.seq_aead_s test1_ciphersuite = (seq8 + 1) in
  let enc_res9 = test_encryption test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_encryption9_aad test1_encryption9_plaintext 9 test1_encryption9_ciphertext test1_encryption9_nonce in

  let exp_res0 = test_export test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_export0_exportContext test1_export0_len test1_export0_exportValue in

  let exp_res1 = test_export test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_export1_exportContext test1_export1_len test1_export1_exportValue in

  let exp_res2 = test_export test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_export2_exportContext test1_export2_len test1_export2_exportValue in

  let exp_res3 = test_export test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_export3_exportContext test1_export3_len test1_export3_exportValue in

  let exp_res4 = test_export test1_ciphersuite test1_key test1_nonce test1_exporterSecret test1_export4_exportContext test1_export4_len test1_export4_exportValue in

  enc_res0 && enc_res1 && enc_res2 && enc_res3 && enc_res4 && enc_res5 && enc_res6 && enc_res7 && enc_res8 && enc_res9 && res && exp_res0 && exp_res1 && exp_res2 && exp_res3 && exp_res4


//
// Main
//


let test () =
  let r1  = test1  () in
  (* let r4  = test4  () in *)
  (* let r8  = test8  () in *)
  (* let r14 = test14 () in *)
  (* let r16 = test16 () in *)
  (* let r20 = test20 () in *)
  (* let r50 = test50 () in *)
  (* let r52 = test52 () in *)
  (* let r56 = test56 () in *)
  (* let r60 = test60 () in *)
  (* let r66 = test66 () in *)
  (* let r70 = test70 () in *)
  (* print "Input limits"; *)
  (* let h0 = Hash.SHA2_256 in *)
  (* let h1 = Hash.SHA2_384 in *)
  (* let h2 = Hash.SHA2_512 in *)

  (* let bl0 = Spec.Hash.Definitions.block_length h0 in *)
  (* let bl1 = Spec.Hash.Definitions.block_length h1 in *)
  (* let bl2 = Spec.Hash.Definitions.block_length h2 in *)

  (* print_bytes "psk" HPKE.size_label_psk_hash HPKE.label_psk_hash; *)
  (* print "\n"; *)

  (* let max_psk_0 = HPKE.max_length_psk h0 in *)
  (* let max_psk_1 = HPKE.max_length_psk h1 in *)
  (* let max_psk_2 = HPKE.max_length_psk h2 in *)

  (* IO.print_uint32_dec (size_to_uint32 max_psk_0); *)
  (* IO.print_uint32_dec (size_to_uint32 max_psk_1); *)
  (* IO.print_uint32_dec (size_to_uint32 max_psk_2); *)

  (* let max_length_psk (cs:ciphersuite) = labeled_extract_max_length_ikm cs size_label_psk_hash *)
  (* let max_length_pskID (cs:ciphersuite) = labeled_extract_max_length_ikm cs size_label_pskID_hash *)
  (* let max_length_info (cs:ciphersuite) = labeled_extract_max_length_ikm cs size_label_info_hash *)
  (* let max_length_exp_ctx (cs:ciphersuite) = labeled_expand_max_length_info cs size_label_sec *)
  r1
  (* && r4 && r8 && r14 && r16 && r20 && r50 && r52 && r56 && r60 && r66 && r70 *)
