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


let test1_pk = List.Tot.map u8_from_UInt8 [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy
]

let test1_context = List.Tot.map u8_from_UInt8 [
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
  0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy
]

//
// Main
//


let cs: Spec.ciphersuite = Spec.DH.DH_Curve25519, Spec.AEAD.AEAD_AES128_GCM, Spec.Hash.SHA2_256

let test () =

  IO.print_string "\nTEST 1\n";
  let test1_pk = of_list test1_pk in
  let test1_context = create 32 (u8 0) in
  Lib.PrintSequence.print_label_lbytes #32 "Random" (Lib.RandomSequence.crypto_random3 32);
  match Spec.ECIES.encap cs test1_pk test1_context with
  | None -> IO.print_string "Error: Spec.ECIES.encap failed\n"
  | Some (k, sk, pk) ->
    Lib.PrintSequence.print_label_lbytes #(Spec.ECIES.size_key cs) "ECIES Secret" k;
    Lib.PrintSequence.print_label_lbytes #(Spec.ECIES.size_key_dh cs) "ECIES Ephemeral Secret" sk;
    Lib.PrintSequence.print_label_lbytes #(Spec.ECIES.size_key_dh cs) "ECIES Ephemeral Public" pk

  (* if r1_a then IO.print_string "\nHKDF Extract: Success!\n" *)
  (* else IO.print_string "\nHKDF Extract: Failure :(\n"; *)
  (* if r1_b then IO.print_string "HKDF Expand: Success!\n" *)
  (* else IO.print_string "HKDF Expand: Failure :(\n"; *)


  (* // Composite result *)
  (* if r1_a && r1_b && r2_a && r2_b && r3_a && r3_b then IO.print_string "\nComposite result: Success!\n" *)
  (* else IO.print_string "\nComposite result: Failure :(\n" *)
