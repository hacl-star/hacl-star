module Hacl.EC.Curve25519_donna_c64.Bigint

open FStar.Mul
open FStar.ST
open FStar.Ghost
open Hacl.UInt8
open Hacl.UInt128
open Hacl.UInt64
open FStar.Buffer
open FStar.Math.Lib
open Hacl.EC.Curve25519.Parameters

(* Module abbreviations *)
module B = FStar.Buffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module H8   = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128

let u8  = U8.t
let u32 = U32.t
let u64 = U64.t

let h8   = H8.t
let h64  = H64.t
let h128 = H128.t


type uint8_p = buffer H8.t
type limb    = H64.t
type felem   = b:buffer limb{length b = 5}


#reset-options "--initial_fuel 0 --max_fuel 0"

let bound h (b:felem) (n:nat{n < 64}) : GTot Type0 =
  live h b /\ v (get h b 0) < pow2 n /\ v (get h b 1) < pow2 n /\ v (get h b 2) < pow2 n
  /\ v (get h b 3) < pow2 n /\ v (get h b 4) < pow2 n 


let eval h (b:felem{live h b}) : GTot nat =
  v (get h b 0) + pow2 51 * v (get h b 1) + pow2 102 * v (get h b 2) + pow2 153 * v (get h b 3)
  + pow2 204 * v (get h b 4)


open FStar.HyperStack

val eval_bytes : h:mem -> b:uint8_p{live h b} -> n:nat{n <= length b} -> GTot nat
let rec eval_bytes h b n =
  match n with
  | 0 -> 0
  | _ -> pow2 (8 * (n-1)) * Hacl.UInt8.v (get h b (n-1)) + eval_bytes h b (n-1)


val eval_eq_lemma: ha:mem -> hb:mem -> a:felem{live ha a} -> b:felem{live hb b} -> Lemma
    (requires ( (forall (i:nat). i < 5 ==> v (get ha a i) = v (get hb b i)) ))
    (ensures ( eval ha a = eval hb b ))
let rec eval_eq_lemma ha hb a b = ()


let eval_5 (x0:H64.t) (x1:H64.t) (x2:H64.t) (x3:H64.t) (x4:H64.t) =
  H64 (v x0 + pow2 51 * v x1 + pow2 102 * v x2 + pow2 153 * v x3 + pow2 204 * v x4)



let lemma_max_uint8 (n:nat) : Lemma
  (requires (n = 8))
  (ensures (pow2 n = 256))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 8 = 256)
let lemma_max_uint32 (n:nat) : Lemma
  (requires (n = 32))
  (ensures (pow2 n = 4294967296))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 32 = 4294967296)
let lemma_max_uint64 (n:nat) : Lemma
  (requires (n = 64))
  (ensures (pow2 n = 18446744073709551616))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 64 = 18446744073709551616)
let lemma_max_uint128 (n:nat) : Lemma
  (requires (n = 128))
  (ensures (pow2 n = 340282366920938463463374607431768211456))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 128 = 340282366920938463463374607431768211456)
let lemma_2_51 (n:nat) : Lemma
  (requires (n = 51))
  (ensures (pow2 n = 2251799813685248))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 51 = 2251799813685248)
let lemma_2_102 (n:nat) : Lemma
  (requires (n = 102))
  (ensures (pow2 n = 5070602400912917605986812821504))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 102 = 5070602400912917605986812821504)
let lemma_2_153 (n:nat) : Lemma 
  (requires (n = 153))
  (ensures (pow2 n = 11417981541647679048466287755595961091061972992))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 153 = 11417981541647679048466287755595961091061972992)
let lemma_2_204 (n:nat) : Lemma 
  (requires (n = 204))
  (ensures (pow2 n = 25711008708143844408671393477458601640355247900524685364822016))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 204 = 25711008708143844408671393477458601640355247900524685364822016)
let lemma_2_255 (n:nat) : Lemma 
  (requires (n = 255))
  (ensures (pow2 n = 57896044618658097711785492504343953926634992332820282019728792003956564819968))
  [SMTPat (pow2 n)]
  = assert_norm(pow2 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968)
