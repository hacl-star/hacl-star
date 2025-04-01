module Hacl.Agile.Hash

open FStar.HyperStack.ST
open FStar.Integers
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

friend EverCrypt.Hash

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

(* Implementation-agile hash state, to provide the `state` field of the
streaming functor instantiation. As said in the fsti, this largely follows EverCrypt.Hash. A TODO would be to figure out if one can build upon the other rather than *)

(* LOLZ: we need to synchronise twice so that the friend above is not shadowing the type impl. *)
let _sync_decl1 = ()
let _sync_decl2 = ()

module H = Spec.Agile.Hash

(* TODO: implement something in krml so that we don't end up with two impl
  enumerations: the impl type, and the tags of the state type, which will be
  absolutely identical... *)

(* Changing the suffix for the constructors to avoid accidental sharing of the tag type with EverCrypt_Hash, which would wreak havoc because EverCrypt_Hash does not have a strong abstraction barrier and includes libintvector.h, unlike this module which includes libintvector-shim.h and has proper isolation from intrinsics. *)
noeq
type state_s : impl -> Type0 =
| MD5_a: p:Hacl.Hash.Definitions.state (| H.MD5, () |) -> state_s MD5
| SHA1_a: p:Hacl.Hash.Definitions.state (| H.SHA1, () |) -> state_s SHA1
| SHA2_224_a: p:Hacl.Hash.Definitions.state (| H.SHA2_224, () |) -> state_s SHA2_224
| SHA2_256_a: p:Hacl.Hash.Definitions.state (| H.SHA2_256, () |) -> state_s SHA2_256
| SHA2_384_a: p:Hacl.Hash.Definitions.state (| H.SHA2_384, () |) -> state_s SHA2_384
| SHA2_512_a: p:Hacl.Hash.Definitions.state (| H.SHA2_512, () |) -> state_s SHA2_512
| SHA3_224_a: p:Hacl.Hash.Definitions.state (| H.SHA3_224, () |) -> state_s SHA3_224
| SHA3_256_a: p:Hacl.Hash.Definitions.state (| H.SHA3_256, () |) -> state_s SHA3_256
| SHA3_384_a: p:Hacl.Hash.Definitions.state (| H.SHA3_384, () |) -> state_s SHA3_384
| SHA3_512_a: p:Hacl.Hash.Definitions.state (| H.SHA3_512, () |) -> state_s SHA3_512
| Blake2S_a: p:Hacl.Hash.Definitions.state H.((|Blake2S, Hacl.Impl.Blake2.Core.M32 |)) -> state_s Blake2S_32
| Blake2S_128_a: s: squash EverCrypt.TargetConfig.hacl_can_compile_vec128 ->
    p:Hacl.Hash.Definitions.state H.((|Blake2S, Hacl.Impl.Blake2.Core.M128 |)) -> state_s (Blake2S_128 s)
| Blake2B_a: p:Hacl.Hash.Definitions.state H.((| Blake2B, Hacl.Impl.Blake2.Core.M32 |)) -> state_s Blake2B_32
| Blake2B_256_a: s: squash EverCrypt.TargetConfig.hacl_can_compile_vec256 ->
    p:Hacl.Hash.Definitions.state H.((| Blake2B, Hacl.Impl.Blake2.Core.M256 |)) -> state_s (Blake2B_256 s)

let invert_state_s (a: impl): Lemma
  (requires True)
  (ensures (inversion (state_s a)))
  [ SMTPat (state_s a) ]
=
  allow_inversion (state_s a)

[@@strict_on_arguments [1]]
inline_for_extraction
let impl_of_state_s (#a: G.erased impl) (s: state_s a): i:impl { i == G.reveal a } =
  match s with
  | MD5_a _ -> MD5
  | SHA1_a _ -> SHA1
  | SHA2_224_a _ -> SHA2_224
  | SHA2_256_a _ -> SHA2_256
  | SHA2_384_a _ -> SHA2_384
  | SHA2_512_a _ -> SHA2_512
  | SHA3_224_a _ -> SHA3_224
  | SHA3_256_a _ -> SHA3_256
  | SHA3_384_a _ -> SHA3_384
  | SHA3_512_a _ -> SHA3_512
  | Blake2S_a _ -> Blake2S_32
  | Blake2S_128_a s _ -> Blake2S_128 s
  | Blake2B_a _ -> Blake2B_32
  | Blake2B_256_a s _ -> Blake2B_256 s

let _: squash (inversion impl) = allow_inversion impl

// Previously: forcing the result type to be GTot since we can't represent D.impl in Low*
// Now: ok to use in inline_for_extraction
inline_for_extraction noextract
let impl_of_impl (i: impl): Hacl.Hash.Definitions.impl =
  match i with
  | MD5 -> (| H.MD5, () |)
  | SHA1 -> (| H.SHA1, () |)
  | SHA2_224 -> (| H.SHA2_224, () |)
  | SHA2_256 -> (| H.SHA2_256, () |)
  | SHA2_384 -> (| H.SHA2_384, () |)
  | SHA2_512 -> (| H.SHA2_512, () |)
  | SHA3_224 -> (| H.SHA3_224, () |)
  | SHA3_256 -> (| H.SHA3_256, () |)
  | SHA3_384 -> (| H.SHA3_384, () |)
  | SHA3_512 -> (| H.SHA3_512, () |)
  | Blake2S_32 -> (| H.Blake2S, Hacl.Impl.Blake2.Core.M32 |)
  | Blake2S_128 _ -> (| H.Blake2S, Hacl.Impl.Blake2.Core.M128 |)
  | Blake2B_32 -> (| H.Blake2B, Hacl.Impl.Blake2.Core.M32 |)
  | Blake2B_256 _ -> (| H.Blake2B, Hacl.Impl.Blake2.Core.M256 |)

[@@strict_on_arguments [1]]
inline_for_extraction
let p #a (s: state_s a): Hacl.Hash.Definitions.state (impl_of_impl (impl_of_state_s #(G.hide a) s)) =
  match s with
  | MD5_a p -> p
  | SHA1_a p -> p
  | SHA2_224_a p -> p
  | SHA2_256_a p -> p
  | SHA2_384_a p -> p
  | SHA2_512_a p -> p
  | SHA3_224_a p -> p
  | SHA3_256_a p -> p
  | SHA3_384_a p -> p
  | SHA3_512_a p -> p
  | Blake2S_a p -> p
  | Blake2S_128_a _ p -> p
  | Blake2B_a p -> p
  | Blake2B_256_a _ p -> p

let freeable_s #a s = B.freeable (p #a s)

let footprint_s #a (s: state_s a) =
  B.loc_addr_of_buffer (p s)

let invariant_s #a (s: state_s a) h =
  B.live h (p s)

let repr #a s h: GTot _ =
  let s = B.get h s 0 in
  as_seq h (p s)

let impl_of_state a s =
  impl_of_state_s #a (!*s)

let repr_eq (#a:impl) (r1 r2: Spec.Hash.Definitions.words_state (alg_of_impl a)) =
  Seq.equal r1 r2

let fresh_is_disjoint l1 l2 h0 h1 = ()

let invariant_loc_in_footprint #a s m = ()

let frame_invariant #a l s h0 h1 =
  let state = B.deref h0 s in
  assert (repr_eq (repr s h0) (repr s h1))

let alloca a =
  let open Hacl.Impl.Blake2.Core in
  let s: state_s a =
    match a with
    | MD5 -> MD5_a (B.alloca 0ul 4ul)
    | SHA1  -> SHA1_a (B.alloca 0ul 5ul)
    | SHA2_224 -> SHA2_224_a (B.alloca 0ul 8ul)
    | SHA2_256 -> SHA2_256_a (B.alloca 0ul 8ul)
    | SHA2_384 -> SHA2_384_a (B.alloca 0UL 8ul)
    | SHA2_512 -> SHA2_512_a (B.alloca 0UL 8ul)
    | SHA3_224 -> SHA3_224_a (B.alloca 0UL 25ul)
    | SHA3_256 -> SHA3_256_a (B.alloca 0UL 25ul)
    | SHA3_384 -> SHA3_384_a (B.alloca 0UL 25ul)
    | SHA3_512 -> SHA3_512_a (B.alloca 0UL 25ul)
    | Blake2S_32 ->
        Blake2S_a (B.alloca 0ul 16ul)
    | Blake2S_128 _ ->
        if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
          Blake2S_128_a () (B.alloca (zero_element Spec.Blake2.Blake2S M128) (impl_state_len (| Blake2S, M128 |)))
        else
          false_elim ()
    | Blake2B_32 ->
        Blake2B_a (B.alloca 0uL 16ul)
    | Blake2B_256 _ ->
        if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
          Blake2B_256_a () (B.alloca (zero_element Spec.Blake2.Blake2B M256) (impl_state_len (| Blake2B, M256 |)))
        else
          false_elim ()
  in
  B.alloca s 1ul

inline_for_extraction noextract
val malloc_helper (#a: impl) (r: HS.rid) (init: impl_word (impl_of_impl a))
  (mk: (b:Hacl.Hash.Definitions.state (impl_of_impl a)) -> Stack (state_s a)
    (requires fun h0 -> True)
    (ensures fun h0 s h1 -> h0 == h1 /\ p s == b)
  ):
  FStar.HyperStack.ST.ST (B.buffer (state_s a))
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if B.g_is_null s then
      B.(modifies loc_none h0 h1)
    else
      B.length s == 1 /\
      invariant s h1 /\
      M.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint s h1) h0 h1 /\
      M.(loc_includes (loc_region_only true r) (footprint s h1)) /\
      freeable h1 s))

let malloc_helper #a r init mk =
  let open Hacl.Streaming.Interface in
  let h0 = ST.get () in
  let s = fallible_malloc r init (impl_state_len (impl_of_impl a)) in
    if B.is_null s then
    B.null
  else
    let s: Hacl.Hash.Definitions.state (impl_of_impl a) = s in
    let st = fallible_malloc r (mk s) 1ul in
    if B.is_null st then (
      B.free s;
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      B.null
    ) else
    st

let malloc_ a r =
  let h0 = ST.get () in
  let open Hacl.Streaming.Interface in
  // NOTE: the helper was a PAIN to write but hopefully it'll make maintenance better
  match a with
  | MD5 -> malloc_helper r 0ul (fun x -> MD5_a x)
  | SHA1 -> malloc_helper r 0ul (fun x -> SHA1_a x)
  | SHA2_224 -> malloc_helper r 0ul (fun x -> SHA2_224_a x)
  | SHA2_256 -> malloc_helper r 0ul (fun x -> SHA2_256_a x)
  | SHA2_384 -> malloc_helper r 0UL (fun x -> SHA2_384_a x)
  | SHA2_512 -> malloc_helper r 0UL (fun x -> SHA2_512_a x)
  | SHA3_224 -> malloc_helper r 0UL (fun x -> SHA3_224_a x)
  | SHA3_256 -> malloc_helper r 0UL (fun x -> SHA3_256_a x)
  | SHA3_384 -> malloc_helper r 0UL (fun x -> SHA3_384_a x)
  | SHA3_512 -> malloc_helper r 0UL (fun x -> SHA3_512_a x)
  | Blake2S_32 -> malloc_helper r 0ul (fun x -> Blake2S_a x)
  | Blake2S_128 _ ->
      // As usual, to prevent linking errors (missing symbols) on systems that
      // do not have this implementation available.
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        let s = Hacl.Blake2s_128.malloc_internal_state_with_key r in
        if B.is_null s then
          B.null
        else
          let st = fallible_malloc r (Blake2S_128_a () s) 1ul in
          if B.is_null st then (
            B.free s;
            let h1 = ST.get () in
            B.(modifies_only_not_unused_in loc_none h0 h1);
            B.null
          ) else
            st
      else
        false_elim ()
  | Blake2B_32 -> malloc_helper r 0UL (fun x -> Blake2B_a x)
  | Blake2B_256 _ ->
      // As usual, to prevent linking errors (missing symbols) on systems that
      // do not have this implementation available.
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        let s = Hacl.Blake2b_256.malloc_internal_state_with_key r in
        if B.is_null s then
          B.null
        else
          let st = fallible_malloc r (Blake2B_256_a () s) 1ul in
          if B.is_null st then (
            B.free s;
            let h1 = ST.get () in
            B.(modifies_only_not_unused_in loc_none h0 h1);
            B.null
          ) else
            st
      else
        false_elim ()

let create_in a r =
  let st = malloc_ a r in
  if B.is_null st then None else Some st

let init #a s =
  match !*s with
  | MD5_a p -> Hacl.Hash.MD5.init p
  | SHA1_a p -> Hacl.Hash.SHA1.init p
  | SHA2_224_a p -> Hacl.Hash.SHA2.init_224 p
  | SHA2_256_a p -> Hacl.Hash.SHA2.init_256 p
  | SHA2_384_a p -> Hacl.Hash.SHA2.init_384 p
  | SHA2_512_a p -> Hacl.Hash.SHA2.init_512 p
  | SHA3_224_a p -> Hacl.Hash.SHA3.init Spec.Agile.Hash.SHA3_224 p
  | SHA3_256_a p -> Hacl.Hash.SHA3.init Spec.Agile.Hash.SHA3_256 p
  | SHA3_384_a p -> Hacl.Hash.SHA3.init Spec.Agile.Hash.SHA3_384 p
  | SHA3_512_a p -> Hacl.Hash.SHA3.init Spec.Agile.Hash.SHA3_512 p
  | Blake2S_a p -> let _ = Hacl.Hash.Blake2s_32.init p in ()
  | Blake2S_128_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        let _ = Hacl.Hash.Blake2s_128.init p in ()
      else
        LowStar.Ignore.ignore p
  | Blake2B_a p -> let _ = Hacl.Hash.Blake2b_32.init p in ()
  | Blake2B_256_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        let _ = Hacl.Hash.Blake2b_256.init p in ()
      else
        LowStar.Ignore.ignore p

let update_multi #a s prevlen blocks len =
  let open Spec.Agile.Hash in
  match !*s with
  | MD5_a p ->
      let n = len / block_len MD5 in
      Hacl.Hash.MD5.update_multi p () blocks n
  | SHA1_a p ->
      let n = len / block_len SHA1 in
      Hacl.Hash.SHA1.update_multi p () blocks n
  | SHA2_224_a p ->
      let n = len / block_len SHA2_224 in
      Hacl.Hash.SHA2.update_multi_224 p () blocks n
  | SHA2_256_a p ->
      let n = len / block_len SHA2_256 in
      Hacl.Hash.SHA2.update_multi_256 p () blocks n
  | SHA2_384_a p ->
      let n = len / block_len SHA2_384 in
      Hacl.Hash.SHA2.update_multi_384 p () blocks n
  | SHA2_512_a p ->
      let n = len / block_len SHA2_512 in
      Hacl.Hash.SHA2.update_multi_512 p () blocks n
  | SHA3_224_a p -> let n = len / block_len SHA3_224 in Hacl.Hash.SHA3.update_multi SHA3_224 p () blocks n
  | SHA3_256_a p -> let n = len / block_len SHA3_256 in Hacl.Hash.SHA3.update_multi SHA3_256 p () blocks n
  | SHA3_384_a p -> let n = len / block_len SHA3_384 in Hacl.Hash.SHA3.update_multi SHA3_384 p () blocks n
  | SHA3_512_a p -> let n = len / block_len SHA3_512 in Hacl.Hash.SHA3.update_multi SHA3_512 p () blocks n
  | Blake2S_a p ->
      let n = len / block_len Blake2S in
      let _ = Hacl.Hash.Blake2s_32.update_multi p prevlen blocks n in
      ()
  | Blake2S_128_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        let n = len / block_len Blake2S in
        // no_inline version otherwise this module (NOT compiled with -mavx,
        // -mavx2, etc.) tries to stack-allocate a Lib.IntVector.vec128
        let _ = Hacl.Hash.Blake2s_128.update_multi_no_inline p prevlen blocks n in
        ()
      else LowStar.Ignore.ignore p
  | Blake2B_a p ->
      [@inline_let] let prevlen = Int.Cast.Full.uint64_to_uint128 prevlen in
      let n = len / block_len Blake2B in
      let _ = Hacl.Hash.Blake2b_32.update_multi p prevlen blocks n in
      ()
  | Blake2B_256_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        [@inline_let] let prevlen = Int.Cast.Full.uint64_to_uint128 prevlen in
        let n = len / block_len Blake2B in
        // Same
        let _ = Hacl.Hash.Blake2b_256.update_multi_no_inline p prevlen blocks n in
        ()
      else LowStar.Ignore.ignore p

let update_last #a s prev_len last last_len =
  [@inline_let] let cast = FStar.Int.Cast.Full.uint64_to_uint128 in
  let open Spec.Agile.Hash in
  match !*s with
  | MD5_a p ->
      Hacl.Hash.MD5.update_last p prev_len last last_len
  | SHA1_a p ->
      Hacl.Hash.SHA1.update_last p prev_len last last_len
  | SHA2_224_a p ->
      Hacl.Hash.SHA2.update_last_224 p prev_len last last_len
  | SHA2_256_a p ->
      Hacl.Hash.SHA2.update_last_256 p prev_len last last_len
  | SHA2_384_a p ->
      Hacl.Hash.SHA2.update_last_384 p (cast prev_len) last last_len
  | SHA2_512_a p ->
      Hacl.Hash.SHA2.update_last_512 p (cast prev_len) last last_len
  | SHA3_224_a p -> Hacl.Hash.SHA3.update_last SHA3_224 p () last last_len
  | SHA3_256_a p -> Hacl.Hash.SHA3.update_last SHA3_256 p () last last_len
  | SHA3_384_a p -> Hacl.Hash.SHA3.update_last SHA3_384 p () last last_len
  | SHA3_512_a p -> Hacl.Hash.SHA3.update_last SHA3_512 p () last last_len
  | Blake2S_a p ->
      Hacl.Hash.Blake2s_32.update_last p prev_len last last_len
  | Blake2S_128_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        Hacl.Hash.Blake2s_128.update_last_no_inline p prev_len last last_len
      else LowStar.Ignore.ignore p
  | Blake2B_a p ->
      Hacl.Hash.Blake2b_32.update_last p (cast prev_len) last last_len
  | Blake2B_256_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        Hacl.Hash.Blake2b_256.update_last_no_inline p (cast prev_len) last last_len
      else LowStar.Ignore.ignore p

let finish #a s dst =
  let open Spec.Agile.Hash in
  match !*s with
  | MD5_a p -> Hacl.Hash.MD5.finish p dst
  | SHA1_a p -> Hacl.Hash.SHA1.finish p dst
  | SHA2_224_a p -> Hacl.Hash.SHA2.finish_224 p dst
  | SHA2_256_a p -> Hacl.Hash.SHA2.finish_256 p dst
  | SHA2_384_a p -> Hacl.Hash.SHA2.finish_384 p dst
  | SHA2_512_a p -> Hacl.Hash.SHA2.finish_512 p dst
  | SHA3_224_a p -> Hacl.Hash.SHA3.finish SHA3_224 p dst
  | SHA3_256_a p -> Hacl.Hash.SHA3.finish SHA3_256 p dst
  | SHA3_384_a p -> Hacl.Hash.SHA3.finish SHA3_384 p dst
  | SHA3_512_a p -> Hacl.Hash.SHA3.finish SHA3_512 p dst
  | Blake2S_a p -> Hacl.Hash.Blake2s_32.finish p dst
  | Blake2S_128_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        Hacl.Hash.Blake2s_128.finish p dst
      else LowStar.Ignore.ignore p
  | Blake2B_a p ->
      Hacl.Hash.Blake2b_32.finish p dst
  | Blake2B_256_a _ p ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        Hacl.Hash.Blake2b_256.finish p dst
      else LowStar.Ignore.ignore p

let free_ #ea s =
  begin match !*s with
  | MD5_a p -> B.free p
  | SHA1_a p -> B.free p
  | SHA2_224_a p -> B.free p
  | SHA2_256_a p -> B.free p
  | SHA2_384_a p -> B.free p
  | SHA2_512_a p -> B.free p
  | SHA3_224_a p -> B.free p
  | SHA3_256_a p -> B.free p
  | SHA3_384_a p -> B.free p
  | SHA3_512_a p -> B.free p
  | Blake2S_a p -> B.free p
  | Blake2S_128_a _ p -> B.free p
  | Blake2B_a p -> B.free p
  | Blake2B_256_a _ p -> B.free p
  end;
  B.free s

let copy #a s_src s_dst =
  match !*s_src with
  | MD5_a p_src ->
      [@inline_let]
      let s_dst: state MD5 = s_dst in
      let p_dst = MD5_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 4ul
  | SHA1_a p_src ->
      [@inline_let]
      let s_dst: state SHA1 = s_dst in
      let p_dst = SHA1_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 5ul
  | SHA2_224_a p_src ->
      [@inline_let]
      let s_dst: state SHA2_224 = s_dst in
      let p_dst = SHA2_224_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA2_256_a p_src ->
      [@inline_let]
      let s_dst: state SHA2_256 = s_dst in
      let p_dst = SHA2_256_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA2_384_a p_src ->
      [@inline_let]
      let s_dst: state SHA2_384 = s_dst in
      let p_dst = SHA2_384_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA2_512_a p_src ->
      [@inline_let]
      let s_dst: state SHA2_512 = s_dst in
      let p_dst = SHA2_512_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 8ul
  | SHA3_224_a p_src ->
      [@inline_let] let s_dst: state SHA3_224 = s_dst in
      let p_dst = SHA3_224_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 25ul
  | SHA3_256_a p_src ->
      [@inline_let] let s_dst: state SHA3_256 = s_dst in
      let p_dst = SHA3_256_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 25ul
  | SHA3_384_a p_src ->
      [@inline_let] let s_dst: state SHA3_384 = s_dst in
      let p_dst = SHA3_384_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 25ul
  | SHA3_512_a p_src ->
      [@inline_let] let s_dst: state SHA3_512 = s_dst in
      let p_dst = SHA3_512_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 25ul
  | Blake2S_a p_src ->
      [@inline_let] let s_dst: state Blake2S_32 = s_dst in
      let p_dst = Blake2S_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 16ul
  | Blake2S_128_a s p_src ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        [@inline_let] let s_dst: state (Blake2S_128 s) = s_dst in
        let p_dst = Blake2S_128_a?.p !*s_dst in
        Hacl.Hash.Blake2s_128.copy_internal_state p_src p_dst
      else
        false_elim ()
  | Blake2B_a p_src ->
      [@inline_let] let s_dst: state Blake2B_32 = s_dst in
      let p_dst = Blake2B_a?.p !*s_dst in
      B.blit p_src 0ul p_dst 0ul 16ul
  | Blake2B_256_a s p_src ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        [@inline_let] let s_dst: state (Blake2B_256 s) = s_dst in
        let p_dst = Blake2B_256_a?.p !*s_dst in
        Hacl.Hash.Blake2b_256.copy_internal_state p_src p_dst
      else
        false_elim ()

let hash i dst input input_len =
  match i with
  | MD5 -> Hacl.Hash.MD5.hash_oneshot dst input input_len
  | SHA1  -> Hacl.Hash.SHA1.hash_oneshot dst input input_len
  | SHA2_224 -> Hacl.Streaming.SHA2.hash_224 dst input input_len
  | SHA2_256 -> Hacl.Streaming.SHA2.hash_256 dst input input_len
  | SHA2_384 -> Hacl.Streaming.SHA2.hash_384 dst input input_len
  | SHA2_512 -> Hacl.Streaming.SHA2.hash_512 dst input input_len
  | SHA3_224 -> Hacl.Hash.SHA3.hash Spec.Agile.Hash.SHA3_224 dst input input_len
  | SHA3_256 -> Hacl.Hash.SHA3.hash Spec.Agile.Hash.SHA3_256 dst input input_len
  | SHA3_384 -> Hacl.Hash.SHA3.hash Spec.Agile.Hash.SHA3_384 dst input input_len
  | SHA3_512 -> Hacl.Hash.SHA3.hash Spec.Agile.Hash.SHA3_512 dst input input_len
  | Blake2S_32 -> Hacl.Hash.Blake2s_32.hash dst input input_len
  | Blake2S_128 _ ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        Hacl.Hash.Blake2s_128.hash dst input input_len
      else
        false_elim ()
  | Blake2B_32 -> Hacl.Hash.Blake2b_32.hash dst input input_len
  | Blake2B_256 _ ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        Hacl.Hash.Blake2b_256.hash dst input input_len
      else
        false_elim ()
