module Spec.P256.Test

open Lib.IntTypes
open Lib.Sequence
open Lib.Meta

open Spec.P256
open Spec.ECDSA.Test.Vectors
open Spec.Hash.Definitions

module PS = Lib.PrintSequence

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

let test_pk_compressed (a:hash_alg_ecdsa) (inp:vec_SigVer) : FStar.All.ML bool =
  let { msg; qx; qy; r; s; result } = inp in
  let msg_len   = String.strlen msg / 2 in
  let pk_x_len  = String.strlen qx / 2 in
  let pk_y_len  = String.strlen qy / 2 in
  let sig_r_len = String.strlen r / 2 in
  let sig_s_len = String.strlen s / 2 in
  let is_valid  = result in

  if not (msg_len <= max_size_t &&
         min_input_length a <= msg_len &&
         pk_x_len = 32 && pk_y_len = 32 &&
         sig_r_len = 32 && sig_s_len = 32)
  then false
  else
    let pk_x = from_hex qx in
    let pk_y = from_hex qy in
    let pk_raw = concat #_ #32 #32 pk_x pk_y in
    let pk_c = pk_compressed_from_raw pk_raw in
    let pk_raw_c = pk_compressed_to_raw pk_c in

    match pk_raw_c with
    | Some pk_raw_c -> PS.print_compare true 64 pk_raw pk_raw_c
    | None -> false


let test_sigver (a:hash_alg_ecdsa) (inp:vec_SigVer) : FStar.All.ML bool =
  let { msg; qx; qy; r; s; result } = inp in
  let msg_len   = String.strlen msg / 2 in
  let pk_x_len  = String.strlen qx / 2 in
  let pk_y_len  = String.strlen qy / 2 in
  let sig_r_len = String.strlen r / 2 in
  let sig_s_len = String.strlen s / 2 in
  let is_valid  = result in

  if not (msg_len <= max_size_t &&
         min_input_length a <= msg_len &&
         pk_x_len = 32 && pk_y_len = 32 &&
         sig_r_len = 32 && sig_s_len = 32)
  then false
  else
    let pk_x = from_hex qx in
    let pk_y = from_hex qy in
    let pk   = concat #_ #32 #32 pk_x pk_y in

    let is_sig_valid =
      ecdsa_verification_agile a msg_len (from_hex msg)
        pk (from_hex r) (from_hex s) in
    is_sig_valid = is_valid


let test_siggen (a:hash_alg_ecdsa) (inp:vec_SigGen) : FStar.All.ML bool =
  let { msg'; d; qx'; qy'; k; r'; s' } = inp in
  let msg_len   = String.strlen msg' / 2 in
  let sk_len    = String.strlen d / 2 in
  let nonce_len = String.strlen k / 2 in
  let pk_x_len  = String.strlen qx' / 2 in
  let pk_y_len  = String.strlen qy' / 2 in
  let sig_r_len = String.strlen r' / 2 in
  let sig_s_len = String.strlen s' / 2 in

  if not (msg_len <= max_size_t &&
         min_input_length a <= msg_len &&
         sk_len = 32 && nonce_len = 32 &&
         pk_x_len = 32 && pk_y_len = 32 &&
         sig_r_len = 32 && sig_s_len = 32)
  then false
  else
    let pk_x = from_hex qx' in
    let pk_y = from_hex qy' in
    let pk   = concat #_ #32 #32 pk_x pk_y in

    let sig_r = from_hex r' in
    let sig_s = from_hex s' in
    let sig_expected = concat #_ #32 #32 sig_r sig_s in

    let is_sig_valid =
      ecdsa_verification_agile a msg_len (from_hex msg')
        pk (from_hex r') (from_hex s') in

    let sig_computed  =
      ecdsa_signature_agile a msg_len (from_hex msg')
        (from_hex d) (from_hex k) in

    let compare_sig =
      if Some? sig_computed then
        PS.print_compare true 64 sig_expected (Some?.v sig_computed)
      else false in

    compare_sig && is_sig_valid


let print_result (b:bool) : FStar.All.ML unit =
  if b then IO.print_string "\nSuccess!\n" else IO.print_string "\nFailure!\n"


let test () : FStar.All.ML bool =
  IO.print_string "\n[P-256 ECDSA-verify with SHA2-256]\n";
  let res1 = List.for_all (test_sigver (Hash SHA2_256)) sigver_vectors_sha2_256 in
  print_result res1;

  IO.print_string "\n[P-256 ECDSA-sign with SHA2-256]\n";
  let res2 = List.for_all (test_siggen (Hash SHA2_256)) siggen_vectors_sha2_256 in
  print_result res2;


  IO.print_string "\n[P-256 ECDSA-verify with SHA2-384]\n";
  let res3 = List.for_all (test_sigver (Hash SHA2_384)) sigver_vectors_sha2_384 in
  print_result res3;

  IO.print_string "\n[P-256 ECDSA-sign with SHA2-384]\n";
  let res4 = List.for_all (test_siggen (Hash SHA2_384)) siggen_vectors_sha2_384 in
  print_result res4;

  IO.print_string "\n[P-256 ECDSA-verify with SHA2-512]\n";
  let res5 = List.for_all (test_sigver (Hash SHA2_512)) sigver_vectors_sha2_512 in
  print_result res5;

  IO.print_string "\n[P-256 ECDSA-sign with SHA2-512]\n";
  let res6 = List.for_all (test_siggen (Hash SHA2_512)) siggen_vectors_sha2_512 in
  print_result res6;

  IO.print_string "\n[P-256 compressed keys]\n";
  let res7 = List.for_all (test_pk_compressed (Hash SHA2_256)) sigver_vectors_sha2_256 in
  print_result res7;

  let res : bool = res1 && res2 && res3 && res4 && res5 && res6 && res7 in
  if res then begin IO.print_string "\n\n[P-256] PASS\n"; true end
  else begin IO.print_string "\n\n[P-256] FAIL\n"; false end
