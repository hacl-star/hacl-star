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
  let pkR = HPKE.deserialize cs pkRm in
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


let test0_mode: HPKE.mode = HPKE.Base
let test0_ciphersuite: HPKE.ciphersuite = DH.DH_Curve25519, Hash.SHA2_256, AEAD.AES128_GCM, Hash.SHA2_256

// generated: "4f6465206f6e2061204772656369616e2055726e"
inline_for_extraction
let size_test0_info: size_nat = 20
let test0_info_list : l:list uint8{List.Tot.length l == size_test0_info} =
  [@inline_let]
  let l = [
    u8 0x4f; u8 0x64; u8 0x65; u8 0x20; u8 0x6f;
    u8 0x6e; u8 0x20; u8 0x61; u8 0x20; u8 0x47;
    u8 0x72; u8 0x65; u8 0x63; u8 0x69; u8 0x61;
    u8 0x6e; u8 0x20; u8 0x55; u8 0x72; u8 0x6e;
  ] in
  assert_norm(List.Tot.length l == size_test0_info);
  l
let test0_info : lbytes size_test0_info = createL test0_info_list

// generated: "6d9014e4609687b0a3670a22f2a14eac5ae6ad8c0beb62fb3ecb13dc8ebf5e06"
inline_for_extraction
let size_test0_ikmR: size_nat = 32
let test0_ikmR_list : l:list uint8{List.Tot.length l == size_test0_ikmR} =
  [@inline_let]
  let l = [
    u8 0x6d; u8 0x90; u8 0x14; u8 0xe4; u8 0x60;
    u8 0x96; u8 0x87; u8 0xb0; u8 0xa3; u8 0x67;
    u8 0x0a; u8 0x22; u8 0xf2; u8 0xa1; u8 0x4e;
    u8 0xac; u8 0x5a; u8 0xe6; u8 0xad; u8 0x8c;
    u8 0x0b; u8 0xeb; u8 0x62; u8 0xfb; u8 0x3e;
    u8 0xcb; u8 0x13; u8 0xdc; u8 0x8e; u8 0xbf;
    u8 0x5e; u8 0x06;
  ] in
  assert_norm(List.Tot.length l == size_test0_ikmR);
  l
let test0_ikmR : lbytes size_test0_ikmR = createL test0_ikmR_list

// generated: "6305de86b3cec022fae6f2f2d2951f0f90c8662112124fd62f17e0a99bdbd08e"
inline_for_extraction
let size_test0_ikmE: size_nat = 32
let test0_ikmE_list : l:list uint8{List.Tot.length l == size_test0_ikmE} =
  [@inline_let]
  let l = [
    u8 0x63; u8 0x05; u8 0xde; u8 0x86; u8 0xb3;
    u8 0xce; u8 0xc0; u8 0x22; u8 0xfa; u8 0xe6;
    u8 0xf2; u8 0xf2; u8 0xd2; u8 0x95; u8 0x1f;
    u8 0x0f; u8 0x90; u8 0xc8; u8 0x66; u8 0x21;
    u8 0x12; u8 0x12; u8 0x4f; u8 0xd6; u8 0x2f;
    u8 0x17; u8 0xe0; u8 0xa9; u8 0x9b; u8 0xdb;
    u8 0xd0; u8 0x8e;
  ] in
  assert_norm(List.Tot.length l == size_test0_ikmE);
  l
let test0_ikmE : lbytes size_test0_ikmE = createL test0_ikmE_list

// generated: "ecaf25b8485bcf40b9f013dbb96a6230f25733b8435bba0997a1dedbc7f78806"
inline_for_extraction
let size_test0_skRm: size_nat = 32
let test0_skRm_list : l:list uint8{List.Tot.length l == size_test0_skRm} =
  [@inline_let]
  let l = [
    u8 0xec; u8 0xaf; u8 0x25; u8 0xb8; u8 0x48;
    u8 0x5b; u8 0xcf; u8 0x40; u8 0xb9; u8 0xf0;
    u8 0x13; u8 0xdb; u8 0xb9; u8 0x6a; u8 0x62;
    u8 0x30; u8 0xf2; u8 0x57; u8 0x33; u8 0xb8;
    u8 0x43; u8 0x5b; u8 0xba; u8 0x09; u8 0x97;
    u8 0xa1; u8 0xde; u8 0xdb; u8 0xc7; u8 0xf7;
    u8 0x88; u8 0x06;
  ] in
  assert_norm(List.Tot.length l == size_test0_skRm);
  l
let test0_skRm : lbytes size_test0_skRm = createL test0_skRm_list

// generated: "6cee2e2755790708a2a1be22667883a5e3f9ec52810404a0d889a0ed3e28de00"
inline_for_extraction
let size_test0_skEm: size_nat = 32
let test0_skEm_list : l:list uint8{List.Tot.length l == size_test0_skEm} =
  [@inline_let]
  let l = [
    u8 0x6c; u8 0xee; u8 0x2e; u8 0x27; u8 0x55;
    u8 0x79; u8 0x07; u8 0x08; u8 0xa2; u8 0xa1;
    u8 0xbe; u8 0x22; u8 0x66; u8 0x78; u8 0x83;
    u8 0xa5; u8 0xe3; u8 0xf9; u8 0xec; u8 0x52;
    u8 0x81; u8 0x04; u8 0x04; u8 0xa0; u8 0xd8;
    u8 0x89; u8 0xa0; u8 0xed; u8 0x3e; u8 0x28;
    u8 0xde; u8 0x00;
  ] in
  assert_norm(List.Tot.length l == size_test0_skEm);
  l
let test0_skEm : lbytes size_test0_skEm = createL test0_skEm_list

// generated: "a5912b20892e36905bac635267e2353d58f8cc7525271a2bf57b9c48d2ec2c07"
inline_for_extraction
let size_test0_pkRm: size_nat = 32
let test0_pkRm_list : l:list uint8{List.Tot.length l == size_test0_pkRm} =
  [@inline_let]
  let l = [
    u8 0xa5; u8 0x91; u8 0x2b; u8 0x20; u8 0x89;
    u8 0x2e; u8 0x36; u8 0x90; u8 0x5b; u8 0xac;
    u8 0x63; u8 0x52; u8 0x67; u8 0xe2; u8 0x35;
    u8 0x3d; u8 0x58; u8 0xf8; u8 0xcc; u8 0x75;
    u8 0x25; u8 0x27; u8 0x1a; u8 0x2b; u8 0xf5;
    u8 0x7b; u8 0x9c; u8 0x48; u8 0xd2; u8 0xec;
    u8 0x2c; u8 0x07;
  ] in
  assert_norm(List.Tot.length l == size_test0_pkRm);
  l
let test0_pkRm : lbytes size_test0_pkRm = createL test0_pkRm_list

// generated: "950897e0d37a8bdb0f2153edf5fa580a64b399c39fbb3d014f80983352a63617"
inline_for_extraction
let size_test0_pkEm: size_nat = 32
let test0_pkEm_list : l:list uint8{List.Tot.length l == size_test0_pkEm} =
  [@inline_let]
  let l = [
    u8 0x95; u8 0x08; u8 0x97; u8 0xe0; u8 0xd3;
    u8 0x7a; u8 0x8b; u8 0xdb; u8 0x0f; u8 0x21;
    u8 0x53; u8 0xed; u8 0xf5; u8 0xfa; u8 0x58;
    u8 0x0a; u8 0x64; u8 0xb3; u8 0x99; u8 0xc3;
    u8 0x9f; u8 0xbb; u8 0x3d; u8 0x01; u8 0x4f;
    u8 0x80; u8 0x98; u8 0x33; u8 0x52; u8 0xa6;
    u8 0x36; u8 0x17;
  ] in
  assert_norm(List.Tot.length l == size_test0_pkEm);
  l
let test0_pkEm : lbytes size_test0_pkEm = createL test0_pkEm_list

// generated: "950897e0d37a8bdb0f2153edf5fa580a64b399c39fbb3d014f80983352a63617"
inline_for_extraction
let size_test0_enc: size_nat = 32
let test0_enc_list : l:list uint8{List.Tot.length l == size_test0_enc} =
  [@inline_let]
  let l = [
    u8 0x95; u8 0x08; u8 0x97; u8 0xe0; u8 0xd3;
    u8 0x7a; u8 0x8b; u8 0xdb; u8 0x0f; u8 0x21;
    u8 0x53; u8 0xed; u8 0xf5; u8 0xfa; u8 0x58;
    u8 0x0a; u8 0x64; u8 0xb3; u8 0x99; u8 0xc3;
    u8 0x9f; u8 0xbb; u8 0x3d; u8 0x01; u8 0x4f;
    u8 0x80; u8 0x98; u8 0x33; u8 0x52; u8 0xa6;
    u8 0x36; u8 0x17;
  ] in
  assert_norm(List.Tot.length l == size_test0_enc);
  l
let test0_enc : lbytes size_test0_enc = createL test0_enc_list

// generated: "799b7b9a6a070e77ee9b9a2032f6624b273b532809c60200eba17ac3baf69a00"
inline_for_extraction
let size_test0_shared_secret: size_nat = 32
let test0_shared_secret_list : l:list uint8{List.Tot.length l == size_test0_shared_secret} =
  [@inline_let]
  let l = [
    u8 0x79; u8 0x9b; u8 0x7b; u8 0x9a; u8 0x6a;
    u8 0x07; u8 0x0e; u8 0x77; u8 0xee; u8 0x9b;
    u8 0x9a; u8 0x20; u8 0x32; u8 0xf6; u8 0x62;
    u8 0x4b; u8 0x27; u8 0x3b; u8 0x53; u8 0x28;
    u8 0x09; u8 0xc6; u8 0x02; u8 0x00; u8 0xeb;
    u8 0xa1; u8 0x7a; u8 0xc3; u8 0xba; u8 0xf6;
    u8 0x9a; u8 0x00;
  ] in
  assert_norm(List.Tot.length l == size_test0_shared_secret);
  l
let test0_shared_secret : lbytes size_test0_shared_secret = createL test0_shared_secret_list

// generated: "002acc146c3ed28a930a50da2b269cb150a8a78a54081f81db457ac52d5bd2f581cb95a2c63b1dac72dc030fbe46d152ccb09f43fdf6e74d13660a4bd80ff49b55"
inline_for_extraction
let size_test0_key_schedule_context: size_nat = 65
let test0_key_schedule_context_list : l:list uint8{List.Tot.length l == size_test0_key_schedule_context} =
  [@inline_let]
  let l = [
    u8 0x00; u8 0x2a; u8 0xcc; u8 0x14; u8 0x6c;
    u8 0x3e; u8 0xd2; u8 0x8a; u8 0x93; u8 0x0a;
    u8 0x50; u8 0xda; u8 0x2b; u8 0x26; u8 0x9c;
    u8 0xb1; u8 0x50; u8 0xa8; u8 0xa7; u8 0x8a;
    u8 0x54; u8 0x08; u8 0x1f; u8 0x81; u8 0xdb;
    u8 0x45; u8 0x7a; u8 0xc5; u8 0x2d; u8 0x5b;
    u8 0xd2; u8 0xf5; u8 0x81; u8 0xcb; u8 0x95;
    u8 0xa2; u8 0xc6; u8 0x3b; u8 0x1d; u8 0xac;
    u8 0x72; u8 0xdc; u8 0x03; u8 0x0f; u8 0xbe;
    u8 0x46; u8 0xd1; u8 0x52; u8 0xcc; u8 0xb0;
    u8 0x9f; u8 0x43; u8 0xfd; u8 0xf6; u8 0xe7;
    u8 0x4d; u8 0x13; u8 0x66; u8 0x0a; u8 0x4b;
    u8 0xd8; u8 0x0f; u8 0xf4; u8 0x9b; u8 0x55;
  ] in
  assert_norm(List.Tot.length l == size_test0_key_schedule_context);
  l
let test0_key_schedule_context : lbytes size_test0_key_schedule_context = createL test0_key_schedule_context_list

// generated: "3ed37d4c4c7e3ebe6cb1fca03eabd4c878b442da340915d51d6ed49d8369d785"
inline_for_extraction
let size_test0_secret: size_nat = 32
let test0_secret_list : l:list uint8{List.Tot.length l == size_test0_secret} =
  [@inline_let]
  let l = [
    u8 0x3e; u8 0xd3; u8 0x7d; u8 0x4c; u8 0x4c;
    u8 0x7e; u8 0x3e; u8 0xbe; u8 0x6c; u8 0xb1;
    u8 0xfc; u8 0xa0; u8 0x3e; u8 0xab; u8 0xd4;
    u8 0xc8; u8 0x78; u8 0xb4; u8 0x42; u8 0xda;
    u8 0x34; u8 0x09; u8 0x15; u8 0xd5; u8 0x1d;
    u8 0x6e; u8 0xd4; u8 0x9d; u8 0x83; u8 0x69;
    u8 0xd7; u8 0x85;
  ] in
  assert_norm(List.Tot.length l == size_test0_secret);
  l
let test0_secret : lbytes size_test0_secret = createL test0_secret_list

// generated: "e20cee1bf5392ad2d3a442e231f187ae"
inline_for_extraction
let size_test0_key: size_nat = 16
let test0_key_list : l:list uint8{List.Tot.length l == size_test0_key} =
  [@inline_let]
  let l = [
    u8 0xe2; u8 0x0c; u8 0xee; u8 0x1b; u8 0xf5;
    u8 0x39; u8 0x2a; u8 0xd2; u8 0xd3; u8 0xa4;
    u8 0x42; u8 0xe2; u8 0x31; u8 0xf1; u8 0x87;
    u8 0xae;
  ] in
  assert_norm(List.Tot.length l == size_test0_key);
  l
let test0_key : lbytes size_test0_key = createL test0_key_list

// generated: "5d99b2f03c452f7a9441933a"
inline_for_extraction
let size_test0_base_nonce: size_nat = 12
let test0_base_nonce_list : l:list uint8{List.Tot.length l == size_test0_base_nonce} =
  [@inline_let]
  let l = [
    u8 0x5d; u8 0x99; u8 0xb2; u8 0xf0; u8 0x3c;
    u8 0x45; u8 0x2f; u8 0x7a; u8 0x94; u8 0x41;
    u8 0x93; u8 0x3a;
  ] in
  assert_norm(List.Tot.length l == size_test0_base_nonce);
  l
let test0_base_nonce : lbytes size_test0_base_nonce = createL test0_base_nonce_list

// generated: "00c3cdacab28e981cc907d12e4f55f0aacae261dbb4eb610447a6bc431bfe2aa"
inline_for_extraction
let size_test0_exporter_secret: size_nat = 32
let test0_exporter_secret_list : l:list uint8{List.Tot.length l == size_test0_exporter_secret} =
  [@inline_let]
  let l = [
    u8 0x00; u8 0xc3; u8 0xcd; u8 0xac; u8 0xab;
    u8 0x28; u8 0xe9; u8 0x81; u8 0xcc; u8 0x90;
    u8 0x7d; u8 0x12; u8 0xe4; u8 0xf5; u8 0x5f;
    u8 0x0a; u8 0xac; u8 0xae; u8 0x26; u8 0x1d;
    u8 0xbb; u8 0x4e; u8 0xb6; u8 0x10; u8 0x44;
    u8 0x7a; u8 0x6b; u8 0xc4; u8 0x31; u8 0xbf;
    u8 0xe2; u8 0xaa;
  ] in
  assert_norm(List.Tot.length l == size_test0_exporter_secret);
  l
let test0_exporter_secret : lbytes size_test0_exporter_secret = createL test0_exporter_secret_list

// generated: "436f756e742d30"
inline_for_extraction
let size_test0_encryption0_aad: size_nat = 7
let test0_encryption0_aad_list : l:list uint8{List.Tot.length l == size_test0_encryption0_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x30;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption0_aad);
  l
let test0_encryption0_aad : lbytes size_test0_encryption0_aad = createL test0_encryption0_aad_list

// generated: "9418f1ae06eddc43aa911032aed4a951754ee2286a786733761857f8d96a7ec8d852da93bc5eeab49623344aba"
inline_for_extraction
let size_test0_encryption0_ciphertext: size_nat = 45
let test0_encryption0_ciphertext_list : l:list uint8{List.Tot.length l == size_test0_encryption0_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x94; u8 0x18; u8 0xf1; u8 0xae; u8 0x06;
    u8 0xed; u8 0xdc; u8 0x43; u8 0xaa; u8 0x91;
    u8 0x10; u8 0x32; u8 0xae; u8 0xd4; u8 0xa9;
    u8 0x51; u8 0x75; u8 0x4e; u8 0xe2; u8 0x28;
    u8 0x6a; u8 0x78; u8 0x67; u8 0x33; u8 0x76;
    u8 0x18; u8 0x57; u8 0xf8; u8 0xd9; u8 0x6a;
    u8 0x7e; u8 0xc8; u8 0xd8; u8 0x52; u8 0xda;
    u8 0x93; u8 0xbc; u8 0x5e; u8 0xea; u8 0xb4;
    u8 0x96; u8 0x23; u8 0x34; u8 0x4a; u8 0xba;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption0_ciphertext);
  l
let test0_encryption0_ciphertext : lbytes size_test0_encryption0_ciphertext = createL test0_encryption0_ciphertext_list

// generated: "5d99b2f03c452f7a9441933a"
inline_for_extraction
let size_test0_encryption0_nonce: size_nat = 12
let test0_encryption0_nonce_list : l:list uint8{List.Tot.length l == size_test0_encryption0_nonce} =
  [@inline_let]
  let l = [
    u8 0x5d; u8 0x99; u8 0xb2; u8 0xf0; u8 0x3c;
    u8 0x45; u8 0x2f; u8 0x7a; u8 0x94; u8 0x41;
    u8 0x93; u8 0x3a;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption0_nonce);
  l
let test0_encryption0_nonce : lbytes size_test0_encryption0_nonce = createL test0_encryption0_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test0_encryption0_plaintext: size_nat = 29
let test0_encryption0_plaintext_list : l:list uint8{List.Tot.length l == size_test0_encryption0_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption0_plaintext);
  l
let test0_encryption0_plaintext : lbytes size_test0_encryption0_plaintext = createL test0_encryption0_plaintext_list

// generated: "436f756e742d31"
inline_for_extraction
let size_test0_encryption1_aad: size_nat = 7
let test0_encryption1_aad_list : l:list uint8{List.Tot.length l == size_test0_encryption1_aad} =
  [@inline_let]
  let l = [
    u8 0x43; u8 0x6f; u8 0x75; u8 0x6e; u8 0x74;
    u8 0x2d; u8 0x31;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption1_aad);
  l
let test0_encryption1_aad : lbytes size_test0_encryption1_aad = createL test0_encryption1_aad_list

// generated: "74d69c61899b9158bb50e95d92fbad106f612ea67c61b3c4bef65c8bf3dc18e17bf41ec4c408688aae58358d0e"
inline_for_extraction
let size_test0_encryption1_ciphertext: size_nat = 45
let test0_encryption1_ciphertext_list : l:list uint8{List.Tot.length l == size_test0_encryption1_ciphertext} =
  [@inline_let]
  let l = [
    u8 0x74; u8 0xd6; u8 0x9c; u8 0x61; u8 0x89;
    u8 0x9b; u8 0x91; u8 0x58; u8 0xbb; u8 0x50;
    u8 0xe9; u8 0x5d; u8 0x92; u8 0xfb; u8 0xad;
    u8 0x10; u8 0x6f; u8 0x61; u8 0x2e; u8 0xa6;
    u8 0x7c; u8 0x61; u8 0xb3; u8 0xc4; u8 0xbe;
    u8 0xf6; u8 0x5c; u8 0x8b; u8 0xf3; u8 0xdc;
    u8 0x18; u8 0xe1; u8 0x7b; u8 0xf4; u8 0x1e;
    u8 0xc4; u8 0xc4; u8 0x08; u8 0x68; u8 0x8a;
    u8 0xae; u8 0x58; u8 0x35; u8 0x8d; u8 0x0e;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption1_ciphertext);
  l
let test0_encryption1_ciphertext : lbytes size_test0_encryption1_ciphertext = createL test0_encryption1_ciphertext_list

// generated: "5d99b2f03c452f7a9441933b"
inline_for_extraction
let size_test0_encryption1_nonce: size_nat = 12
let test0_encryption1_nonce_list : l:list uint8{List.Tot.length l == size_test0_encryption1_nonce} =
  [@inline_let]
  let l = [
    u8 0x5d; u8 0x99; u8 0xb2; u8 0xf0; u8 0x3c;
    u8 0x45; u8 0x2f; u8 0x7a; u8 0x94; u8 0x41;
    u8 0x93; u8 0x3b;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption1_nonce);
  l
let test0_encryption1_nonce : lbytes size_test0_encryption1_nonce = createL test0_encryption1_nonce_list

// generated: "4265617574792069732074727574682c20747275746820626561757479"
inline_for_extraction
let size_test0_encryption1_plaintext: size_nat = 29
let test0_encryption1_plaintext_list : l:list uint8{List.Tot.length l == size_test0_encryption1_plaintext} =
  [@inline_let]
  let l = [
    u8 0x42; u8 0x65; u8 0x61; u8 0x75; u8 0x74;
    u8 0x79; u8 0x20; u8 0x69; u8 0x73; u8 0x20;
    u8 0x74; u8 0x72; u8 0x75; u8 0x74; u8 0x68;
    u8 0x2c; u8 0x20; u8 0x74; u8 0x72; u8 0x75;
    u8 0x74; u8 0x68; u8 0x20; u8 0x62; u8 0x65;
    u8 0x61; u8 0x75; u8 0x74; u8 0x79;
  ] in
  assert_norm(List.Tot.length l == size_test0_encryption1_plaintext);
  l
let test0_encryption1_plaintext : lbytes size_test0_encryption1_plaintext = createL test0_encryption1_plaintext_list
// generated: ""
inline_for_extraction
let size_test0_export0_exporter_context: size_nat = 0
let test0_export0_exporter_context_list : l:list uint8{List.Tot.length l == size_test0_export0_exporter_context} =
  [@inline_let]
  let l = [

  ] in
  assert_norm(List.Tot.length l == size_test0_export0_exporter_context);
  l
let test0_export0_exporter_context : lbytes size_test0_export0_exporter_context = createL test0_export0_exporter_context_list

// generated: "be82c06bd83fd6edd74385de5a70859b9e03def4c7bb224a10cfae86087f8a25"
inline_for_extraction
let size_test0_export0_exported_value: size_nat = 32
let test0_export0_exported_value_list : l:list uint8{List.Tot.length l == size_test0_export0_exported_value} =
  [@inline_let]
  let l = [
    u8 0xbe; u8 0x82; u8 0xc0; u8 0x6b; u8 0xd8;
    u8 0x3f; u8 0xd6; u8 0xed; u8 0xd7; u8 0x43;
    u8 0x85; u8 0xde; u8 0x5a; u8 0x70; u8 0x85;
    u8 0x9b; u8 0x9e; u8 0x03; u8 0xde; u8 0xf4;
    u8 0xc7; u8 0xbb; u8 0x22; u8 0x4a; u8 0x10;
    u8 0xcf; u8 0xae; u8 0x86; u8 0x08; u8 0x7f;
    u8 0x8a; u8 0x25;
  ] in
  assert_norm(List.Tot.length l == size_test0_export0_exported_value);
  l
let test0_export0_exported_value : lbytes size_test0_export0_exported_value = createL test0_export0_exported_value_list

let test0_export0_len:size_nat = 32
// generated: "00"
inline_for_extraction
let size_test0_export1_exporter_context: size_nat = 1
let test0_export1_exporter_context_list : l:list uint8{List.Tot.length l == size_test0_export1_exporter_context} =
  [@inline_let]
  let l = [
    u8 0x00;
  ] in
  assert_norm(List.Tot.length l == size_test0_export1_exporter_context);
  l
let test0_export1_exporter_context : lbytes size_test0_export1_exporter_context = createL test0_export1_exporter_context_list

// generated: "82cbfd3c2b2db75e2311d457e569cf12b6387eb4309bca8e77adb2f2b599fc85"
inline_for_extraction
let size_test0_export1_exported_value: size_nat = 32
let test0_export1_exported_value_list : l:list uint8{List.Tot.length l == size_test0_export1_exported_value} =
  [@inline_let]
  let l = [
    u8 0x82; u8 0xcb; u8 0xfd; u8 0x3c; u8 0x2b;
    u8 0x2d; u8 0xb7; u8 0x5e; u8 0x23; u8 0x11;
    u8 0xd4; u8 0x57; u8 0xe5; u8 0x69; u8 0xcf;
    u8 0x12; u8 0xb6; u8 0x38; u8 0x7e; u8 0xb4;
    u8 0x30; u8 0x9b; u8 0xca; u8 0x8e; u8 0x77;
    u8 0xad; u8 0xb2; u8 0xf2; u8 0xb5; u8 0x99;
    u8 0xfc; u8 0x85;
  ] in
  assert_norm(List.Tot.length l == size_test0_export1_exported_value);
  l
let test0_export1_exported_value : lbytes size_test0_export1_exported_value = createL test0_export1_exported_value_list

let test0_export1_len:size_nat = 32


let test0 () =
  assert (size_test0_key_schedule_context = HPKE.size_ks_ctx test0_ciphersuite);
  let res = test_setupBase test0_ciphersuite test0_skEm test0_pkEm test0_skRm test0_pkRm test0_info test0_enc test0_shared_secret test0_key_schedule_context test0_secret test0_key test0_base_nonce test0_exporter_secret test0_encryption0_nonce test0_encryption1_nonce in
  let seq0:HPKE.seq_aead_s test0_ciphersuite = 0 in
  let enc_res0 = test_encryption test0_ciphersuite test0_key test0_base_nonce test0_exporter_secret test0_encryption0_aad test0_encryption0_plaintext seq0 test0_encryption0_ciphertext test0_encryption0_nonce in

  assert_norm (1 < pow2 (8 * 12));
  let seq1:HPKE.seq_aead_s test0_ciphersuite = (seq0 + 1) in
  let enc_res1 = test_encryption test0_ciphersuite test0_key test0_base_nonce test0_exporter_secret test0_encryption1_aad test0_encryption1_plaintext seq1 test0_encryption1_ciphertext test0_encryption1_nonce in


  let exp_res0 = test_export test0_ciphersuite test0_key test0_base_nonce test0_exporter_secret test0_export0_exporter_context test0_export0_len test0_export0_exported_value in

  let exp_res1 = test_export test0_ciphersuite test0_key test0_base_nonce test0_exporter_secret test0_export1_exporter_context test0_export1_len test0_export1_exported_value in

  enc_res0 && enc_res1 && res && exp_res0 && exp_res1


//
// Main
//


let test () =
  let r1  = test0  () in
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

(* Execute it using make in the hacl-star root directory test-ml-Spec_HPKE_Test *)
