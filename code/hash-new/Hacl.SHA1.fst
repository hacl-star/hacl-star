module Hacl.SHA1

include Hacl.Hash.Common
open Spec.Hash.Helpers

module B = LowStar.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.SHA1
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module CE = C.Endianness

friend Spec.SHA1

(** Top-level constant arrays for the MD5 algorithm. *)
let h0 = IB.igcmalloc_of_list HS.root Spec.init_as_list


let alloca () =
  B.alloca_of_list Spec.init_as_list

let static_fp () =
  B.loc_addr_of_buffer h0

let recall_static_fp () =
  B.recall h0

let init s =
  IB.recall_contents h0 (Seq.seq_of_list Spec.init_as_list);
  B.blit h0 0ul s 0ul 5ul

let working_state_matches (h: HS.mem) (w: Spec.working_state) (s: state SHA1) : GTot Type0 =
  let s' = B.as_seq h s in
  w.Spec.a == Seq.index s' 0 /\
  w.Spec.b == Seq.index s' 1 /\
  w.Spec.c == Seq.index s' 2 /\
  w.Spec.d == Seq.index s' 3 /\
  w.Spec.e == Seq.index s' 4

inline_for_extraction
let w_t = (b: B.lbuffer (word SHA1) 80)

inline_for_extraction
let block_t = (block: B.buffer U8.t { B.length block == size_block SHA1 } )

let w_inv (h0: HS.mem) (h: HS.mem) (m: block_t) (b: w_t) (i: nat) : GTot Type0 =
  B.disjoint m b /\
  B.live h0 m /\
  B.live h m /\
  B.live h b /\
  B.modifies (B.loc_buffer b) h0 h /\ (
    let mi = E.seq_uint32_of_be size_block_w (B.as_seq h0 m) in
    let s = B.as_seq h b in
    (forall (j: nat) . (j < i /\ j < 80) ==> Spec.w mi (U32.uint_to_t j) == Seq.index s j)
  )

inline_for_extraction
let index_32_be' (n: Ghost.erased nat) (b: B.buffer UInt8.t) (i: UInt32.t):
  HST.Stack UInt32.t
    (requires (fun h ->
      B.live h b /\ B.length b == 4 `Prims.op_Multiply` Ghost.reveal n /\
      UInt32.v i < Ghost.reveal n))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (E.seq_uint32_of_be (Ghost.reveal n) (B.as_seq h0 b)) (UInt32.v i)))
= CE.index_32_be b i

inline_for_extraction
let w_body_value (h0: HS.mem) (m: block_t) (b: w_t) (i: U32.t) : HST.Stack U32.t
  (requires (fun h -> w_inv h0 h m b (U32.v i) /\ U32.v i < 80))
  (ensures (fun h v h' -> B.modifies B.loc_none h h' /\ v == Spec.w (E.seq_uint32_of_be size_block_w (B.as_seq h0 m)) i))
= if U32.lt i 16ul
  then
    index_32_be' (Ghost.hide size_block_w) m i
  else
    let wmit3 = B.index b (i `U32.sub` 3ul) in
    let wmit8 = B.index b (i `U32.sub` 8ul) in
    let wmit14 = B.index b (i `U32.sub` 14ul) in
    let wmit16 = B.index b (i `U32.sub` 16ul) in
    Spec.rotl 1ul (wmit3 `U32.logxor` wmit8 `U32.logxor` wmit14 `U32.logxor` wmit16)

(*
let w_body (h0: HS.mem) (m: block_t) (b: w_t) (i: U32.t) : HST.Stack unit
  (requires (fun h -> w_inv h0 h m b (U32.v i) /\ U32.v i < 80))
  (ensures (fun _ _ h' -> w_inv h0 h' m b (U32.v i + 1)))
= if U32.lt i 16ul
  then B.upd b i (CE.index_32_be m i)
  else
    let wmit3 = B.index b (i `U32.sub` 3ul) in
    let wmit8 = B.index b (i `U32.sub` 8ul) in
    let wmit14 = B.index b (i `U32.sub` 14ul) in
    let wmit16 = B.index b (i `U32.sub` 16ul) in
    let v = Spec.rotl 1ul (wmit3 `U32.logxor` wmit8 `U32.logxor` wmit14 `U32.logxor` wmit16) in
    B.upd b i v
