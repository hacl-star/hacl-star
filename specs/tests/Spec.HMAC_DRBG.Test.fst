module Spec.HMAC_DRBG.Test

open FStar.Seq
open Lib.IntTypes
open Lib.Meta

open Spec.Agile.HMAC
open Spec.HMAC_DRBG
open Spec.HMAC_DRBG.Test.Vectors

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 50"

let print_and_compare (len:size_nat) (test_expected test_result:lbytes len) : All.ML bool =
  // Cheap alternative to friend Lib.IntTypes / Lib.RawIntTypes
  assume (squash (uint8 == UInt8.t));
  IO.print_string "\n\nResult:   ";
  List.iter (fun a -> IO.print_uint8_hex_pad a) (seq_to_list test_result);
  IO.print_string "\nExpected: ";
  List.iter (fun a -> IO.print_uint8_hex_pad a) (seq_to_list test_expected);
  Lib.ByteSequence.lbytes_eq #len test_expected test_result

let test_vec
  {a; entropy_input; entropy_input_reseed; nonce; personalization_string;
   additional_input_reseed; additional_input_1; additional_input_2;
   returned_bits}
=
  let returned_bytes_len       = String.strlen returned_bits / 2 in
  let entropy_input_len        = String.strlen entropy_input / 2 in
  let entropy_input_reseed_len = String.strlen entropy_input_reseed / 2 in
  let nonce_len                = String.strlen nonce / 2 in
  let personalization_string_len = String.strlen personalization_string / 2 in
  let additional_input_reseed_len = String.strlen additional_input_reseed / 2 in
  let additional_input_1_len   = String.strlen additional_input_1 / 2 in
  let additional_input_2_len   = String.strlen additional_input_2 / 2 in
  let returned_bits_len        = String.strlen returned_bits / 2 in
  if not (is_supported_alg a &&
          min_length a <= entropy_input_len &&
          entropy_input_len <= max_length &&
          min_length a / 2 <= nonce_len &&
          nonce_len <= max_length &&
          personalization_string_len <= max_personalization_string_length &&
          entropy_input_reseed_len <= max_length &&
          additional_input_reseed_len <= max_additional_input_length &&
          additional_input_1_len <= max_additional_input_length &&
          additional_input_2_len <= max_additional_input_length &&
          0 < returned_bits_len &&
          returned_bits_len <= max_output_length)
  then false
  else
    let _ = hmac_input_bound a in
    let st = instantiate #a
      (from_hex entropy_input) (from_hex nonce) (from_hex personalization_string)
    in
    let st = reseed st
      (from_hex entropy_input_reseed) (from_hex additional_input_reseed)
    in
    match generate st returned_bytes_len (from_hex additional_input_1) with
    | None -> false
    | Some (_, st) ->
      match generate st returned_bytes_len (from_hex additional_input_2) with
      | None -> false
      | Some (out, st) -> print_and_compare returned_bytes_len (from_hex returned_bits) out

let test () =
  let result = List.for_all test_vec test_vectors in
  if result then
    begin
    IO.print_string "\n\n[HMAC-DRBG] PASS\n";
    true
    end
  else
    begin
    IO.print_string "\n\n[HMAC-DRBG] FAIL\n";
    false
    end
