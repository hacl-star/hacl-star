module Tests.SPARKLE

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


#reset-options "--z3rlimit 100 --max_fuel 0"


//
// Test 1
//

(* let test1_plaintext_list  = List.Tot.map u8_from_UInt8 [ *)
(*   0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy; 0x09uy; 0x0Auy; 0x0Buy; 0x0 *)


(* 000102030405060708090A0B0C0D0E0F *)

(* ] *)
(* let test1_plaintext : lbytes 3 = *)
(*   assert_norm (List.Tot.length test1_plaintext_list = 3); *)
(*   of_list test1_plaintext_list *)

(* let test1_expected_list = List.Tot.map u8_from_UInt8 [ *)
(*   0x50uy; 0x8Cuy; 0x5Euy; 0x8Cuy; 0x32uy; 0x7Cuy; 0x14uy; 0xE2uy; *)
(*   0xE1uy; 0xA7uy; 0x2Buy; 0xA3uy; 0x4Euy; 0xEBuy; 0x45uy; 0x2Fuy; *)
(*   0x37uy; 0x45uy; 0x8Buy; 0x20uy; 0x9Euy; 0xD6uy; 0x3Auy; 0x29uy; *)
(*   0x4Duy; 0x99uy; 0x9Buy; 0x4Cuy; 0x86uy; 0x67uy; 0x59uy; 0x82uy; *)
(* ] *)
(* let test1_expected : lbytes 32 = *)
(*   assert_norm (List.Tot.length test1_expected_list = 32); *)
(*   of_list test1_expected_list *)



(* Count = 30 *)
(* Key = 000102030405060708090A0B0C0D0E0F *)
(* Nonce = 000102030405060708090A0B0C0D0E0F *)
(* PT =  *)
(* AD = 000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C *)
(* CT = 958BFC45FFC6C79D8A29BFD9FE60BBD5 *)
