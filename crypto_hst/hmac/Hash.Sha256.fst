module Hash.Sha256

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open Hacl.SBuffer


(* Define base types *)
let u32 = FStar.UInt32.t
let uint32s = Hacl.SBuffer.u32s
let bytes = Hacl.SBuffer.u8s


(* Define algorithm parameters *)
let hashsize = 32ul


(* Define SHA2 functions *)
assume val init : state:uint32s
  -> STL unit
        (requires (fun h -> live h state))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))


assume val update : (state :uint32s) ->
                    (data  :bytes {disjoint state data}) ->
                    (len   :u32)
  -> STL unit
        (requires (fun h -> live h state /\ live h data))
        (ensures  (fun h0 r h1 -> live h1 state /\ live h1 data /\ modifies_1 state h0 h1))


assume val finish: (hash  :bytes   { length hash >= v hashsize }) ->
                   (state :uint32s { disjoint state hash })
  -> STL unit
        (requires (fun h -> live h hash /\ live h state))
        (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 state /\ modifies_2 hash state h0 h1))


assume val sha256 : (hash:bytes { length hash >= v hashsize }) ->
                    (data:bytes { disjoint hash data }) ->
                    (len :u32   { length data = v len })
  -> STL unit
        (requires (fun h -> live h hash /\ live h data))
        (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 data /\ modifies_1 hash h0 h1))
