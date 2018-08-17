module Hacl.SHA2

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2.Constants
module S = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module T = FStar.Tactics

open Spec.Hash.Helpers
open LowStar.BufferOps

friend Spec.SHA2

(** Top-level constant arrays for the various SHA2 algorithms. *)

(* NOTE: we don't have monotonicity yet so there will be various assumes. *)
let h224 = B.gcmalloc_of_list HS.root C.h224_l
let h256 = B.gcmalloc_of_list HS.root C.h256_l
let h384 = B.gcmalloc_of_list HS.root C.h384_l
let h512 = B.gcmalloc_of_list HS.root C.h512_l

let k224_256 = B.gcmalloc_of_list HS.root C.k224_256_l
let k384_512 = B.gcmalloc_of_list HS.root C.k384_512_l

(* We believe it'll be hard to get, "for free", within this module:
     readonly h224 /\ writable client_state ==> disjoint h224 client_state
   so, instead, we require the client to do a little bit of reasoning to show
   that their buffers are disjoint from our top-level readonly state. *)

(* The total footprint of our morally readonly data. *)
let static_fp () =
  M.loc_union
    (M.loc_union (M.loc_addr_of_buffer k224_256) (M.loc_addr_of_buffer k384_512))
    (M.loc_union
      (M.loc_union (M.loc_addr_of_buffer h224) (M.loc_addr_of_buffer h256))
      (M.loc_union (M.loc_addr_of_buffer h384) (M.loc_addr_of_buffer h512)))

let loc_in (l: M.loc) (h: HS.mem) =
  M.(loc_not_unused_in h `loc_includes` l)

(* A useful lemma for clients, to be called at any time before performing an
   allocation, hence giving them "for free" that their allocation is disjoint from
   our top-level arrays. *)
val recall_static_fp: unit -> ST.Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    M.(modifies loc_none h0 h1) /\
    static_fp () `loc_in` h1))

let recall_static_fp () =
  B.recall h224;
  B.recall h256;
  B.recall h384;
  B.recall h512;
  B.recall k224_256;
  B.recall k384_512

(* This succeeds: *)
(* let test (): ST.St unit =
  recall_static_fp ();
  let b = B.malloc HS.root 0ul 1ul in
  assert M.(loc_disjoint (loc_addr_of_buffer b) (static_fp ())) *)

let alloca a () =
  [@ inline_let ]
  let l: list (word a) = Spec.(match a with
    | SHA2_224 -> C.h224_l
    | SHA2_256 -> C.h256_l
    | SHA2_384 -> C.h384_l
    | SHA2_512 -> C.h512_l) in
  B.alloca_of_list l

let alloca_224: alloca_t SHA2_224 =
  T.(synth_by_tactic (specialize (alloca SHA2_224) [`%alloca]))
let alloca_256: alloca_t SHA2_256 =
  T.(synth_by_tactic (specialize (alloca SHA2_256) [`%alloca]))
let alloca_384: alloca_t SHA2_384 =
  T.(synth_by_tactic (specialize (alloca SHA2_384) [`%alloca]))
let alloca_512: alloca_t SHA2_512 =
  T.(synth_by_tactic (specialize (alloca SHA2_512) [`%alloca]))

#set-options "--max_fuel 0 --max_ifuel 0"

let init a s =
  match a with
  | SHA2_224 ->
      B.recall h224;
      // waiting for monotonicity:
      let h = ST.get () in
      assume (B.as_seq h h224 == S.seq_of_list C.h224_l);
      B.blit h224 0ul s 0ul 8ul
  | SHA2_256 ->
      B.recall h256;
      // waiting for monotonicity:
      let h = ST.get () in
      assume (B.as_seq h h256 == S.seq_of_list C.h256_l);
      B.blit h256 0ul s 0ul 8ul
  | SHA2_384 ->
      B.recall h384;
      // waiting for monotonicity:
      let h = ST.get () in
      assume (B.as_seq h h384 == S.seq_of_list C.h384_l);
      B.blit h384 0ul s 0ul 8ul
  | SHA2_512 ->
      B.recall h512;
      // waiting for monotonicity:
      let h = ST.get () in
      assume (B.as_seq h h512 == S.seq_of_list C.h512_l);
      B.blit h512 0ul s 0ul 8ul

let init_224: init_t SHA2_224 =
  T.(synth_by_tactic (specialize (init SHA2_224) [`%init]))
let init_256: init_t SHA2_256 =
  T.(synth_by_tactic (specialize (init SHA2_256) [`%init]))
let init_384: init_t SHA2_384 =
  T.(synth_by_tactic (specialize (init SHA2_384) [`%init]))
let init_512: init_t SHA2_512 =
  T.(synth_by_tactic (specialize (init SHA2_512) [`%init]))

let block_w (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = size_block_w }

#set-options "--max_fuel 1"

val ws (a: sha2_alg) (b: block_w a) (t: U32.t { U32.v t < Spec.size_k_w a }):
  ST.Stack (word a)
    (requires (fun h -> B.live h b))
    (ensures (fun h0 w h1 ->
      B.live h1 b /\
      M.(modifies loc_none h0 h1) /\
      w == Spec.ws a (B.as_seq h0 b) (U32.v t)))
let rec ws a b t =
  if U32.lt t 16ul then
    b.(t)
  else
    let t16 = ws a b (U32.sub t 16ul) in
    let t15 = ws a b (U32.sub t 15ul) in
    let t7  = ws a b (U32.sub t 7ul) in
    let t2  = ws a b (U32.sub t 2ul) in

    let s1 = Spec._sigma1 a t2 in
    let s0 = Spec._sigma0 a t15 in
    Spec.word_add_mod a s1 (Spec.word_add_mod a t7 (Spec.word_add_mod a s0 t16))

#set-options "--max_fuel 0"

let hash_w (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = size_hash_w a }

val shuffle_core (a: sha2_alg)
  (block: block_w a)
  (hash: hash_w a)
  (t: U32.t { U32.v t < Spec.size_k_w a }):
  ST.Stack unit
    (requires (fun h ->
      B.live h block /\ B.live h hash /\
      B.disjoint block hash))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer hash) h0 h1) /\
      B.as_seq h1 hash == Spec.shuffle_core a (B.as_seq h0 block) (B.as_seq h0 hash) (U32.v t)))
