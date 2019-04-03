module Spec.HPKE.CFRG.Test

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

module Spec = Spec.HPKE.CFRG


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
  let skR = of_list test1_sk in
  let pkR = Spec.DH.secret_to_public (Spec.HPKE.curve_of_cs cs) skR in
  let info = create 32 (u8 0x00) in
  let aad = create 32 (u8 0x01) in
  let pt = create 32 (u8 0xFF) in
  let ct, pkE = Spec.HPKE.CFRG.encrypt cs e pkR info aad pt in
  match Spec.HPKE.CFRG.decrypt cs skR pkE info aad ct with
  | None -> IO.print_string "\nHPKE: Failure\n"
  | Some out ->
    let result = for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) pt out in
    if result then IO.print_string "\nHPKE: Success\n"
    else IO.print_string "\nHPKE: Failure\n"
