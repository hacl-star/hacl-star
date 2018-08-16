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
let static_fp =
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
    static_fp `loc_in` h1))

let recall_static_fp () =
  B.recall h224;
  B.recall h256;
  B.recall h384;
  B.recall h512;
  B.recall k224_256;
  B.recall k384_512;
  let h = ST.get () in
  assert (M.loc_union
    (M.loc_union (M.loc_addr_of_buffer k224_256) (M.loc_addr_of_buffer k384_512))
    (M.loc_union
      (M.loc_union (M.loc_addr_of_buffer h224) (M.loc_addr_of_buffer h256))
      (M.loc_union (M.loc_addr_of_buffer h384) (M.loc_addr_of_buffer h512))) `loc_in` h);
  admit ()

(* This succeeds: *)
(* let test (): ST.St unit =
  recall_static_fp ();
  let b = B.malloc HS.root 0ul 1ul in
  assert M.(loc_disjoint (loc_addr_of_buffer b) static_fp) *)

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

let init a s =
  match a with
  | SHA2_224 -> B.recall h224; B.blit h224 0ul s 0ul 8ul
  | SHA2_256 -> B.recall h256; B.blit h256 0ul s 0ul 8ul
  | SHA2_384 -> B.recall h384; B.blit h384 0ul s 0ul 8ul
  | SHA2_512 -> B.recall h512; B.blit h512 0ul s 0ul 8ul

let init_224: init_t Spec.SHA2_224 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_224) [`%init]))
let init_256: init_t Spec.SHA2_256 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_256) [`%init]))
let init_384: init_t Spec.SHA2_384 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_384) [`%init]))
let init_512: init_t Spec.SHA2_512 =
  T.(synth_by_tactic (specialize (init Spec.SHA2_512) [`%init]))

