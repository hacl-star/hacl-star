module Hacl.Operations.Pure

open FStar.Seq
open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open FStar.UInt32


(* Define base types *)
let u8 = FStar.UInt8.t
let u32 = FStar.UInt32.t
let s32 = Hacl.UInt32.t
let bytes = Seq.seq Hacl.UInt8.t


(* Define word functions *)
let rotate_right (a:s32) (b:u32{v b <= 32}) : Tot s32 =
  Hacl.UInt32.logor (Hacl.UInt32.shift_right a b) (Hacl.UInt32.shift_left a (FStar.UInt32.sub 32ul b))


(* Define helper xor function *)
assume val xor_bytes: a:bytes -> b:bytes -> len:u32{v len <= Seq.length a /\ v len <= Seq.length b} 
  -> Tot (output:bytes{Seq.length output = v len})


assume val setall: (b:bytes) -> (l:nat{Seq.length b = l}) -> (x:u8) -> Tot (bf:bytes{Seq.length bf = l})
