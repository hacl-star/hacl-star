module Hacl.Operations.Pure

open FStar.Seq
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32

module I8 = FStar.UInt8
module I32 = FStar.UInt32
module IB = FStar.Buffer



(* Define base types *)
let i8 = FStar.UInt8.t
let i32 = FStar.UInt32.t
let buf32 = Seq.seq i32
let bytes = Seq.seq i8


(* Define word functions *)
let rotate_right (a:i32) (b:i32{v b <= 32}) : Tot i32 =
  I32.logor (I32.shift_right a b) (I32.shift_left a (I32.sub 32ul b))


(* Define helper xor function *)
assume val xor_bytes: a:bytes -> b:bytes -> len:nat{len <= Seq.length a /\ len <= Seq.length b}
  -> Tot (output:bytes{Seq.length output = len})


assume val setall: (b:bytes) -> (l:nat{Seq.length b = l}) -> (x:i8) -> Tot (bf:bytes{Seq.length bf = l})
