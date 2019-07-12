module Spec.HPKE.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module Spec = Spec.HPKE


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

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_sk = of_list test1_sk in
  let test1_pk = Spec.DH.secret_to_public (Spec.HPKE.curve_of_cs cs) test1_sk in
  let test1_context = create 32 (u8 0) in
  let test1_input = create 32 (u8 0xFF) in
  (match Spec.HPKE.encap cs e test1_pk test1_context with
  | _, None -> IO.print_string "Error: Spec.HPKE.encap failed\n"
  | _, Some (ek, epk) -> (
    Lib.PrintSequence.print_label_lbytes #(Spec.HPKE.size_key cs) "\nHPKE Encap Secret" ek;
    IO.print_newline ();
    Lib.PrintSequence.print_label_lbytes #(Spec.HPKE.size_key_dh cs) "\nHPKE Encap Ephemeral Public" epk);
    IO.print_newline ();
    let ciphertext = Spec.HPKE.encrypt cs ek test1_input lbytes_empty (u32 0) in
    Lib.PrintSequence.print_label_lbytes #(32 + Spec.AEAD.size_tag Spec.AEAD.AEAD_AES128_GCM) "\nHPKE Ciphertext" ciphertext;
    IO.print_newline ();
    match Spec.HPKE.decap cs test1_sk epk test1_context with
    | None -> IO.print_string "\nError: Spec.HPKE.decap failed\n"
    | Some dk -> (
      Lib.PrintSequence.print_label_lbytes #(Spec.HPKE.size_key cs) "\nHPKE Decap Secret" dk;
      IO.print_newline ();
      let result_decap = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) ek dk in
      if result_decap then ()
      else IO.print_string "\nHPKE Decap: Failure\n";
      match Spec.HPKE.decrypt cs dk ciphertext lbytes_empty (u32 0) with
      | None -> IO.print_string "\nError: Spec.HPKE.decrypt failed\n"
      | Some plaintext ->
        Lib.PrintSequence.print_label_lbytes #32 "\nHPKE Computed Plaintext" plaintext;
        IO.print_newline ();
        let result_decrypt = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_input plaintext in
        if result_decap then ()
        else IO.print_string "\nHPKE Decap: Failure\n";

        if result_decap && result_decrypt
        then IO.print_string "\nComposite result: Success! \o/ \n"
        else IO.print_string "\nComposite result: Failure :(\n"
    )
  )
