module Spec.ECIES.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module Spec = Spec.ECIES


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
  let test1_pk = Spec.DH.secret_to_public (Spec.ECIES.curve_of_cs cs) test1_sk in
  let test1_context = create 32 (u8 0) in
  let test1_input = create 32 (u8 0xFF) in
  (match Spec.ECIES.encap cs e test1_pk test1_context with
  | _, None -> IO.print_string "Error: Spec.ECIES.encap failed\n"
  | _, Some (ek, epk) -> (
    Lib.PrintSequence.print_label_lbytes #(Spec.ECIES.size_key cs) "\nECIES Encap Secret" ek;
    IO.print_newline ();
    Lib.PrintSequence.print_label_lbytes #(Spec.ECIES.size_key_dh cs) "\nECIES Encap Ephemeral Public" epk);
    IO.print_newline ();
    let ciphertext = Spec.ECIES.encrypt cs ek test1_input lbytes_empty (u32 0) in
    Lib.PrintSequence.print_label_lbytes #(32 + Spec.AEAD.size_tag Spec.AEAD.AEAD_AES128_GCM) "\nECIES Ciphertext" ciphertext;
    IO.print_newline ();
    match Spec.ECIES.decap cs test1_sk epk test1_context with
    | None -> IO.print_string "\nError: Spec.ECIES.decap failed\n"
    | Some dk -> (
      Lib.PrintSequence.print_label_lbytes #(Spec.ECIES.size_key cs) "\nECIES Decap Secret" dk;
      IO.print_newline ();
      let result_decap = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) ek dk in
      if result_decap then ()
      else IO.print_string "\nECIES Decap: Failure\n";
      match Spec.ECIES.decrypt cs dk ciphertext lbytes_empty (u32 0) with
      | None -> IO.print_string "\nError: Spec.ECIES.decrypt failed\n"
      | Some plaintext ->
        Lib.PrintSequence.print_label_lbytes #32 "\nECIES Computed Plaintext" plaintext;
        IO.print_newline ();
        let result_decrypt = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) test1_input plaintext in
        if result_decap then ()
        else IO.print_string "\nECIES Decap: Failure\n";

        if result_decap && result_decrypt
        then IO.print_string "\nComposite result: Success! \o/ \n"
        else IO.print_string "\nComposite result: Failure :(\n"
    )
  )
