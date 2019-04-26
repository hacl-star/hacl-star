module Spec.HPKE.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module Spec = Spec.HPKE

let dflag:bool = false

//
// Test 1
//


let test1_sk = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy
]

let test1_context = List.Tot.map u8_from_UInt8 [
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy;
  0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy
]

//
// Main
//

assume val e: Lib.RandomSequence.entropy

let cs: Spec.ciphersuite = Spec.DH.DH_Curve25519, Spec.AEAD.AEAD_AES128_GCM, Spec.Hash.SHA2_256



val test1: unit -> FStar.All.ML bool
let test1 () =
  let test1_sk = of_list test1_sk in
  let test1_pk = Spec.DH.secret_to_public (Spec.HPKE.curve_of_cs cs) test1_sk in
  let test1_context = create 32 (u8 0) in
  let test1_input = create 32 (u8 0xFF) in
  (match Spec.HPKE.encap cs e test1_pk test1_context with
  | _, None -> IO.print_string "Error: Spec.HPKE.encap failed\n"; false
  | _, Some (ek, epk) -> (
    Lib.PrintSequence.print_label_lbytes dflag "\nHPKE Encap Secret" (Spec.HPKE.size_key cs) ek;
    Lib.PrintSequence.print_label_lbytes dflag "\nHPKE Encap Ephemeral Public" (Spec.HPKE.size_key_dh cs) epk);
    let output = Spec.HPKE.encrypt cs ek test1_input lbytes_empty (u32 0) in
    let ciphertext = sub #uint8 #(32 + Spec.AEAD.size_tag Spec.AEAD.AEAD_AES128_GCM) output 0 32 in
    let tag = sub #uint8 #(32 + Spec.AEAD.size_tag Spec.AEAD.AEAD_AES128_GCM) output 32 (Spec.AEAD.size_tag Spec.AEAD.AEAD_AES128_GCM) in
    Lib.PrintSequence.print_label_lbytes dflag "\nHPKE Output" (32 + Spec.AEAD.size_tag Spec.AEAD.AEAD_AES128_GCM) output;
    match Spec.HPKE.decap cs test1_sk epk test1_context with
    | None -> IO.print_string "\nError: Spec.HPKE.decap failed\n"; false
    | Some dk -> (
      Lib.PrintSequence.print_label_lbytes dflag "\nHPKE Decap Secret" (Spec.HPKE.size_key cs) dk;
      let result_decap = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) ek dk in
      if result_decap then ()
      else IO.print_string "\nHPKE Decap: Failure\n";
      match Spec.HPKE.decrypt cs dk ciphertext tag lbytes_empty (u32 0) with
      | None -> IO.print_string "\nError: Spec.HPKE.decrypt failed\n"; false
      | Some plaintext ->
        Lib.PrintSequence.print_label_lbytes dflag "\nHPKE Computed Plaintext" 32 plaintext;
        let result_decrypt = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_input plaintext in
        if result_decap then ()
        else IO.print_string "\nHPKE Decap: Failure\n";

        if result_decap && result_decrypt
        then (IO.print_string "\nSuccess - Spec.HPKE.Test.test1"; true)
        else (IO.print_string "\nFailure - Spec.HPKE.Test.test1"; false)
    )
  )


val test2: unit -> FStar.All.ML bool
let test2 () =
  let test2_sk = of_list test1_sk in
  let test2_pk = Spec.DH.secret_to_public (Spec.HPKE.curve_of_cs cs) test2_sk in
  let test2_context = create 32 (u8 0) in
  let test2_input = create 128 (u8 0xFF) in
  match Spec.HPKE.encrypt_single e cs test2_pk test2_input test2_context with
  | e, None -> IO.print_string "\nFailure - Encryption failed"; false
  | e, Some output ->
    match Spec.HPKE.decrypt_single cs test2_sk output test2_context with
    | None -> IO.print_string "\nFailure - Decryption failed"; false
    | Some plaintext ->
        Lib.PrintSequence.print_label_lbytes dflag "\nHPKE Computed Plaintext" 32 plaintext;
        let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test2_input plaintext in
        if result
        then (IO.print_string "\nSuccess - Spec.HPKE.Test.test2"; true)
        else (IO.print_string "\nFailure - Spec.HPKE.Test.test2"; false)


let test () =
  let res = true && test1 () in
  let res = res && test2 () in
  if res then (IO.print_string "\n\nComposite result: Success! - Spec.HPKE.Test\n")
  else (IO.print_string "\n\nComposite result: Failure! - Spec.HPKE.Test\n")
