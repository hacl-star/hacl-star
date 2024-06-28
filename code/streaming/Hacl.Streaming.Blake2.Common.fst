module Hacl.Streaming.Blake2.Common

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module LS = Lib.Sequence
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module I = Hacl.Streaming.Interface
module ST = FStar.HyperStack.ST

open FStar.Mul

module Loops = Lib.LoopCombinators

/// Opening a bunch of modules for Blake2
/// =====================================

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

unfold noextract
let size_nat = Lib.IntTypes.size_nat

unfold noextract
let max_key = Spec.Blake2.max_key

unfold noextract
let lbytes = Lib.ByteSequence.lbytes

module Spec = Spec.Blake2
module Core = Hacl.Impl.Blake2.Core
module P = Hacl.Streaming.Blake2.Params
open Hacl.Impl.Blake2.Generic

/// An instance of the stateful type class for blake2
/// =================================================

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

inline_for_extraction noextract
let alg = Spec.alg

inline_for_extraction noextract
let m_spec = Core.m_spec

inline_for_extraction noextract
let index = Params.index

inline_for_extraction noextract
let singleton x' = x:UInt8.t { x == x' }

inline_for_extraction noextract
let singleton_b x' = x:bool { x == x' }

/// The stateful state: (wv, hash).
///
/// This CANNOT be turned into a struct because right now, this type undergoes
/// monomorphization because state_p a is truly indexed over a. (If it were a
/// struct, we'd have to use the same trick we've used elsewhere, where two
/// dummy type arguments are added in order to make sure it monomorphizes à la
/// ML).
inline_for_extraction noextract
let s (a : alg) (i: index a) (m : m_spec) = singleton (i.key_length) & singleton (i.digest_length) & singleton_b (i.last_node) & Core.(state_p a m & state_p a m)

inline_for_extraction noextract
let t (a : alg) = Spec.key_length_t a & Spec.digest_length_t a & bool & Spec.state a

(* In the internal state, we keep wv, the working vector. It's essentially
temporary scratch space that the Blake2 implementation expects to receive. (Why
is the implementation not performing its own stack allocations? Don't know!) *)
inline_for_extraction noextract
let get_wv (#a : alg) #i (#m : m_spec) (s : s a i m) : Tot (Core.state_p a m) =
  match s with _, _, _, (wv, _) -> wv

inline_for_extraction noextract
let get_state_p (#a : alg) (#i: index a) (#m : m_spec) (s : s a i m) : Tot (Core.state_p a m) =
  match s with _, _, _, (_, p) -> p

(* But the working vector is not reflected in the state at all -- it doesn't
have meaningful specification contents. *)
inline_for_extraction noextract
let state_v (#a : alg) (#i: index a) (#m : m_spec) (h : HS.mem) (s : s a i m) : GTot (Spec.state a) =
  Core.state_v h (get_state_p s)

inline_for_extraction noextract
let s_v (#a : alg) (#i: index a) (#m : m_spec) (h : HS.mem) (s : s a i m) : GTot (t a) =
  let kk, nn, last_node, _ = s in
  kk, nn, last_node, state_v h s

/// Small helper which facilitates inferencing implicit arguments for buffer
/// operations
inline_for_extraction noextract
let state_to_lbuffer (#a : alg) (#m : m_spec) (s : Core.state_p a m) :
  B.lbuffer (Core.element_t a m) (4 * U32.v (Core.row_len a m)) =
  s

// For everything to type-check together, this needs use `index`, above, but the
// `snd` part of the index is irrelevant.
inline_for_extraction noextract
let stateful_blake2 (a : alg) (m : m_spec) : I.stateful (index a) =
  I.Stateful
    (fun i -> s a i m) (* s *)
    (* footprint *)
    (fun #_ _ acc ->
      let _, _, _, (wv, b) = acc in
      B.loc_union
       (B.loc_addr_of_buffer (state_to_lbuffer wv))
       (B.loc_addr_of_buffer (state_to_lbuffer b)))
    (* freeable *)
    (fun #_ _ acc ->
      let _, _, _, (wv, b) = acc in
      B.freeable (state_to_lbuffer wv) /\
      B.freeable (state_to_lbuffer b))
    (* invariant *)
    (fun #_ h acc ->
      let _, _, _, (wv, b) = acc in
      B.live h (state_to_lbuffer wv) /\
      B.live h (state_to_lbuffer b) /\
      B.disjoint (state_to_lbuffer wv) (state_to_lbuffer b))
    (fun _ -> t a) (* t *)
    (fun _ h acc -> s_v h acc) (* v *)
    (fun #_ h acc -> let _, _, _, (wv, b) = acc in ()) (* invariant_loc_in_footprint *)
    (fun #_ l acc h0 h1 -> let _, _, _, (wv, b) = acc in ()) (* frame_invariant *)
    (fun #_ _ _ _ _ -> ()) (* frame_freeable *)
    (* alloca *)
    (fun i ->
      let wv = Core.alloc_state a m in
      let b = Core.alloc_state a m in
      i.key_length, i.digest_length, i.last_node, (wv, b))
    (* create_in *)
    (fun i r ->
      let wv = B.malloc r (Core.zero_element a m) U32.(4ul *^ Core.row_len a m) in
      let b = B.malloc r (Core.zero_element a m) U32.(4ul *^ Core.row_len a m) in
      i.key_length, i.digest_length, i.last_node, (wv, b))
    (* free *)
    (fun _ acc ->
      match acc with _, _, _, (wv, b) ->
      B.free (state_to_lbuffer wv);
      B.free (state_to_lbuffer b))
    (* copy *)
    (fun _ src dst ->
      match src with _, _, _, (src_wv, src_b) ->
      match dst with _, _, _, (src_wv, dst_b) ->
      B.blit (state_to_lbuffer src_b) 0ul (state_to_lbuffer dst_b) 0ul
             U32.(4ul *^ Core.row_len a m))

/// Stateful key
/// ============

inline_for_extraction noextract
let key_size (a : alg) = kk:nat{kk <= Spec.max_key a}

/// Defining stateful keys
let params_and_key (a : alg) (i: index a): Type =
  P.params a i & (b:B.buffer uint8 { B.length b == UInt8.v (i.key_length)})

let key_footprint =
  fun #a (#i: index a) h (s: params_and_key a i) ->
    let p, s = s in
    P.footprint #a h p `B.loc_union` (
    if i.key_length = 0uy then B.loc_none else B.loc_addr_of_buffer (s <: B.buffer uint8))

let key_invariant =
  fun #a (#i: index a) h (s: params_and_key a i) ->
    let kk = i.key_length in
    let nn = i.digest_length in
    let p = fst s in
    let s = snd s in
    P.invariant #a #i h p /\
    (kk <> 0uy ==>
      B.live h (s <: B.buffer uint8) /\
      B.loc_disjoint (B.loc_addr_of_buffer (s <: B.buffer uint8)) (P.footprint #a h p))

let key_freeable =
  fun #a (#i: index a) h (s: params_and_key a i) ->
    let kk = i.key_length in
    let nn = i.digest_length in
    let p, s = s in
    P.freeable #a h p /\ (
    if kk = 0uy then True else B.freeable (s <: B.buffer uint8))

let params_t a (i: index a) =
  p:Spec.blake2_params a { p.key_length == i.key_length /\ p.digest_length == i.digest_length }

let key_t #a (i: index a) =
  params_t a i & s:S.seq uint8 { S.length s == UInt8.v (i.key_length) }

let key_v #a (i: index a) h (s: params_and_key a i): GTot (key_t i) =
  let p, s = s in
  P.v #a h p, (if i.key_length = 0uy then S.empty #uint8 else B.as_seq h (s <: B.buffer uint8))

/// Keeps the key and its length at run-time, for extraction, but makes sure the
/// parameter is ghost to let the functor decide, via the index, which APIs need
/// a run-time key and which don't. It's a little bit of work to make it all
/// work out statefully, but is definitely needed in order to pass the key &
/// params for initialization functions (malloc, alloca, reset).
#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"
inline_for_extraction noextract
let stateful_key (a : alg):
  I.stateful (index a) =
  I.Stateful
    (fun i -> params_and_key a i)
    (* footprint *)
    (key_footprint #a)
    (* freeable *)
    (key_freeable #a)
    (* invariant *)
    (key_invariant #a)
    (* t *)
    (key_t #a)
    (* v *)
    (key_v #a)
    (fun #i h s ->
      let p, s = s in
      P.invariant_loc_in_footprint #a h p) (* invariant_loc_in_footprint *)
    (fun #i l (s: params_and_key a i) h0 h1 ->
      let p, _ = s in
      P.frame_invariant #a l p h0 h1) (* frame_invariant *)
    (fun #_ l s h0 h1 ->
      let p, _ = s in
      P.frame_freeable #a l p h0 h1) (* frame_freeable *)

    (* alloca *)
    (fun i ->
      if i.key_length = 0uy then
        let h0 = ST.get () in
        let p = P.alloca a i in
        let s = B.null #uint8 in
        let s = p, s in
        let h1 = ST.get () in
        assert (key_footprint #a #i h1 s == P.footprint h1 p);
        s
      else
        let h0 = ST.get () in
        let p = P.alloca a i in
        let h00 = ST.get () in
        assert P.(invariant h00 p);
        let h01 = ST.get () in
        assert P.(invariant h01 p);

        let s_ = B.alloca (Lib.IntTypes.u8 0) (FStar.Int.Cast.uint8_to_uint32 (i.key_length)) in
        let s = p, s_ in
        let h1 = ST.get () in
        assert B.(modifies loc_none h0 h01);
        assert B.(modifies loc_none h01 h1);
        P.frame_invariant #a B.loc_none p h01 h1;
        assert B.(key_footprint #a #i h1 s == P.footprint h1 p `loc_union` (loc_addr_of_buffer (s_ <: B.buffer uint8)));
        assert (key_invariant #a #i h1 s);
        assert B.(fresh_loc (key_footprint #a #i h1 s) h0 h1);
        assert B.(loc_includes (loc_region_only true (HS.get_tip h1)) (key_footprint #a #i h1 s));
        s)

    (* create_in *)
    (fun i r ->
      if i.key_length = 0uy then
        let h0 = ST.get () in
        let p = P.create_in a i r in
        let s = B.null #uint8 in
        let s = p, s in
        let h1 = ST.get () in
        assert (key_footprint #a #i h1 s == P.footprint h1 p);
        s
      else
        let h0 = ST.get () in
        let p = P.create_in a i r in
        let h01 = ST.get () in
        let s_ = B.malloc r (Lib.IntTypes.u8 0) (FStar.Int.Cast.uint8_to_uint32 (i.key_length)) in
        let s = p, s_ in
        let h1 = ST.get () in
        P.frame_invariant #a B.loc_none p h01 h1;
        assert B.(key_footprint #a #i h1 s == P.footprint h1 p `loc_union` (loc_addr_of_buffer (s_ <: B.buffer uint8)));
        assert (key_invariant #a #i h1 s);
        assert B.(modifies loc_none h0 h01);
        assert B.(modifies loc_none h01 h1);
        assert B.(fresh_loc (key_footprint #a #i h1 s) h0 h1);
        assert B.(loc_includes (loc_region_only true r) (key_footprint #a #i h1 s));
        assert (key_freeable #a #i h1 s);
        s)

    (* free *)
    (fun (i: G.erased (index a)) (s: params_and_key a i) ->
      let p, s = s in
      let kk = (P.get_params p).key_length in
      assert (kk = (G.reveal i).key_length);
      P.free #a p;
      if kk = 0uy then () else B.free (s <: B.buffer uint8))

    (* copy *)
    (fun i (s_src': params_and_key a i) (s_dst': params_and_key a i) ->
      let p_src, s_src = s_src' in
      let kk = (P.get_params p_src).key_length in
      assert (kk = (G.reveal i).key_length);
      let p_dst, s_dst = s_dst' in
      let h0 = ST.get () in
      if kk <> 0uy then begin
        B.blit (s_src <: B.buffer uint8) 0ul
          (s_dst <: B.buffer uint8) 0ul (FStar.Int.Cast.uint8_to_uint32 kk);
        let h1 = ST.get () in
        P.frame_invariant #a (B.loc_addr_of_buffer s_dst) p_src h0 h1;
        P.frame_invariant #a (B.loc_addr_of_buffer s_dst) p_dst h0 h1;
        assert (key_invariant #a #i h1 s_dst')
      end;
      P.copy p_src p_dst;
      let h2 = ST.get () in
      assert (B.as_seq h0 s_src `Seq.equal` B.as_seq h2 s_dst);
      assert (key_v #a i h2 s_dst' == key_v #a i h0 s_src')
      )

inline_for_extraction noextract
let k = stateful_key

/// Actual functor instantiation
/// ============================

/// Small helpers
/// -------------

noextract
let max_input_length (a : alg) : n:nat { n <= Spec.max_limb a /\ n > Spec.size_block a } =
  assert_norm (pow2 64 < pow2 128);
  pow2 64 - 1

noextract inline_for_extraction
let max_input_len (a: alg): (x:U64.t { U64.v x == max_input_length a }) = 0xffffffffffffffffUL

inline_for_extraction noextract
let block (a : alg) = (block: S.seq uint8 { S.length block = Spec.size_block a })

inline_for_extraction noextract
let block_len (a : alg) : U32.t = Core.size_block a

/// From the functor-provided previous length (uint64, public) to a suitable
/// type for Blake2 (secret uint64/uint128)
inline_for_extraction noextract
let blake2_prevlen (a : alg)
                   (prevlen : U64.t{ U64.v prevlen <= max_input_length a}) :
  x:Spec.limb_t a {
    Lib.IntTypes.uint_v x = U64.v prevlen } =
  let open Lib.IntTypes in
  match a with
  | Spec.Blake2S -> to_u64 #U64 #PUB prevlen
  | Spec.Blake2B ->
    [@inline_let] let x : uint64 = to_u64 #U64 #PUB prevlen in
    Lib.IntTypes.cast U128 SEC x

/// Specs
/// -----

noextract
let init_s (a : alg) (p: Spec.blake2_params a) :
  Tot (Spec.state a) =
  Spec.blake2_init_hash a p

noextract
let update_multi_s (#a : alg) (acc : Spec.state a)
                   (prevlen : nat{prevlen % Spec.size_block a = 0})
                   (input : Seq.seq uint8{ prevlen + S.length input <= max_input_length a /\
                                           S.length input % Spec.size_block a = 0 }) :
  Tot (Spec.state a)
=
  let nb = S.length input / U32.v (block_len a) in
  Lib.LoopCombinators.repeati nb (Spec.blake2_update1 a prevlen input) acc

noextract
let update_last_s (#a : alg)
                  (last_node: bool)
                  (acc : Spec.state a)
                  (prevlen : nat{prevlen % Spec.size_block a = 0})
                  (input : Seq.seq uint8{ S.length input + prevlen <= max_input_length a /\
                                          S.length input <= Spec.size_block a }) :
  Tot (Spec.state a) =
  Spec.blake2_update_last a last_node prevlen (S.length input) input acc

noextract
let finish_s (#a : alg) (p: Spec.blake2_params a) (acc : Spec.state a) :
  output : S.seq uint8 { S.length output = UInt8.v p.digest_length } =
  Spec.blake2_finish a acc (UInt8.v p.digest_length)

noextract
let spec_s (a : alg)
  (p: Spec.blake2_params a)
  (last_node: bool)
  (key : lbytes (UInt8.v p.key_length))
  (input : S.seq uint8{if p.key_length = 0uy then S.length input <= max_input_length a else S.length input + Spec.size_block a <= max_input_length a}) =
  Spec.blake2 a last_node input p key

/// Interlude for spec proofs
/// -------------------------

val update_multi_zero:
  #a : alg ->
  acc:Spec.state a ->
  prevlen:nat{prevlen % Spec.size_block a = 0} ->
  Lemma
  (requires (prevlen <= max_input_length a))
  (ensures (update_multi_s #a acc prevlen S.empty == acc))

let update_multi_zero #a acc prevlen =
  Lib.LoopCombinators.eq_repeati0 (0 / U32.v (block_len a)) (Spec.blake2_update1 a prevlen S.empty) acc

#push-options "--z3cliopt smt.arith.nl=false"
val update_multi_associative:
  #a : alg ->
  acc: Spec.state a ->
  prevlen1:nat ->
  prevlen2:nat ->
  input1:S.seq uint8 ->
  input2:S.seq uint8 ->
  Lemma
  (requires (
    (**) Math.Lemmas.pos_times_pos_is_pos Spec.size_block_w (Spec.size_word a);
    prevlen1 % Spec.size_block a = 0 /\
    S.length input1 % Spec.size_block a = 0 /\
    S.length input2 % Spec.size_block a = 0 /\
    prevlen1 + S.length input1 + S.length input2 <= max_input_length a /\
    prevlen2 = prevlen1 + S.length input1))
  (ensures (
    let input = S.append input1 input2 in
    S.length input % Spec.size_block a = 0 /\
    prevlen2 % Spec.size_block a = 0 /\
    update_multi_s (update_multi_s acc prevlen1 input1) prevlen2 input2 ==
      update_multi_s acc prevlen1 input))
#pop-options

#push-options "--z3rlimit 400"
let update_multi_associative #a acc prevlen1 prevlen2 input1 input2 =
  let input = S.append input1 input2 in
  let nb = S.length input / U32.v (block_len a) in
  let nb1 = S.length input1 / U32.v (block_len a) in
  let nb2 = S.length input2 / U32.v (block_len a) in
  let f = Spec.blake2_update1 a prevlen1 input in
  let f1 = Spec.blake2_update1 a prevlen1 input1 in
  let f2 = Spec.blake2_update1 a prevlen2 input2 in
  let aux1 (i:nat{i < nb1}) (acc:Spec.state a) : Lemma (f i acc == f1 i acc)
    = assert (Spec.get_blocki a input i `Seq.equal` Spec.get_blocki a input1 i)
  in
  let aux2 (i:nat{i < nb2}) (acc:Spec.state a) : Lemma (f2 i acc == f (i + nb1) acc)
    = assert (Spec.get_blocki a input2 i `Seq.equal` Spec.get_blocki a input (i + nb1))
  in
  let open Lib.LoopCombinators in
  let open Lib.Sequence.Lemmas in
  calc (==) {
    update_multi_s (update_multi_s acc prevlen1 input1) prevlen2 input2;
    (==) { }
    repeati nb2 f2 (repeati nb1 f1 acc);
    (==) {
      Classical.forall_intro_2 aux1;
      repeati_extensionality nb1 f1 f acc
    }
    repeati nb2 f2 (repeati nb1 f acc);
    (==) {
      repeati_def nb1 f acc;
      repeati_def nb2 f2 (repeat_right 0 nb1 (fixed_a (Spec.state a)) f acc)
    }
    repeat_right 0 nb2 (fixed_a (Spec.state a)) f2 (repeat_right 0 nb1 (fixed_a (Spec.state a)) f acc);
    (==) {
      Classical.forall_intro_2 aux2;
      repeat_gen_right_extensionality nb2 nb1 (fixed_a (Spec.state a)) (fixed_a (Spec.state a)) f2 f (repeat_right 0 nb1 (fixed_a (Spec.state a)) f acc)
    }
    repeat_right nb1 (nb1 + nb2) (fixed_a (Spec.state a)) f (repeat_right 0 nb1 (fixed_a (Spec.state a)) f acc);
    (==) { repeat_right_plus 0 nb1 nb (fixed_a (Spec.state a)) f acc; repeati_def nb f acc }
    repeati nb f acc;
    (==) { }
    update_multi_s acc prevlen1 input;
  }
#pop-options

/// A helper function: the hash incremental function defined with the functions
/// locally defined (with a signature adapted to the functor).
noextract
val blake2_hash_incremental_s :
  a : alg ->
  p: Spec.blake2_params a ->
  last_node: bool ->
  k: lbytes (UInt8.v p.key_length) ->
  input:S.seq uint8 { if p.key_length = 0uy then S.length input <= max_input_length a else S.length input + (Spec.size_block a) <= max_input_length a } ->
  output:S.seq uint8 { S.length output = UInt8.v p.digest_length }

#push-options "--z3cliopt smt.arith.nl=false"
let blake2_hash_incremental_s a p last_node k input0 =
  let key_block = if UInt8.v p.key_length > 0 then Spec.blake2_key_block a (UInt8.v p.key_length) k else S.empty in
  let key_block_len = S.length key_block in
  let input = Seq.append key_block input0 in
  assert (key_block_len = (if p.key_length = 0uy then 0 else Spec.size_block a));
  (**) Math.Lemmas.modulo_lemma 0 (U32.v (block_len a));
  let bs, l = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let acc1 = init_s a p in
  let acc2 = update_multi_s #a acc1 0 bs in
  let acc3 = update_last_s #a last_node acc2 (S.length bs) l in
  let acc4 = finish_s #a p acc3 in
  acc4
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
val repeati_split_at_eq :
  a : alg ->
  s : Spec.state a ->
  input:S.seq uint8 { S.length input <= max_input_length a } ->
  Lemma(
    let n_blocks, l_last = Spec.split a (S.length input) in
    let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
    n_blocks = Lib.Sequence.length blocks / Spec.size_block a /\ // This is necessary for type-checking
    Lib.LoopCombinators.repeati n_blocks (Spec.blake2_update1 a 0 input) s ==
        Lib.LoopCombinators.repeati n_blocks (Spec.blake2_update1 a 0 blocks) s)
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
let repeati_split_at_eq a s input =
  let n_blocks, l_last = Spec.split a (S.length input) in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let f = Spec.blake2_update1 a 0 input in
  let g = Spec.blake2_update1 a 0 blocks in
  let s1 = Lib.LoopCombinators.repeati n_blocks f s in
  assert (Lib.Sequence.length blocks = n_blocks * Spec.size_block a);
  Math.Lemmas.cancel_mul_div n_blocks (Spec.size_block a);
  assert (n_blocks = Lib.Sequence.length blocks / Spec.size_block a);
  assert (Lib.Sequence.length blocks <= max_input_length a);
  let s2 = Lib.LoopCombinators.repeati n_blocks g s in
  assert (input `Seq.equal` Seq.append blocks last);
  assert (S.length input = S.length blocks + S.length last);
  introduce forall (i:nat{i < n_blocks}). (Spec.get_blocki a input i) `S.equal` (Spec.get_blocki a blocks i)
  with
    begin
    let b0 = Spec.get_blocki a input i in
    let b1 = Spec.get_blocki a blocks i in
    assert (S.length blocks = n_blocks * Spec.size_block a);
    Math.Lemmas.lemma_mult_le_right (Spec.size_block a) (i + 1) n_blocks;
    assert ((i + 1) * Spec.size_block a <= S.length blocks);
    Math.Lemmas.lemma_mult_le_right (Spec.size_block a) i n_blocks;
    assert (i * Spec.size_block a <= S.length blocks);
    Math.Lemmas.distributivity_add_left i 1 (Spec.size_block a);
    assert ((i + 1) * Spec.size_block a = i * Spec.size_block a + Spec.size_block a);
    introduce forall (j:  nat{j < Spec.size_block a}). S.index b0 j == S.index b1 j
    with
      begin
      assert (i * Spec.size_block a + j < i * Spec.size_block a + Spec.size_block a);
      Math.Lemmas.nat_times_nat_is_nat i (Spec.size_block a);
      S.lemma_index_slice input (i * Spec.size_block a) ((i + 1) * Spec.size_block a) j;
      assert (S.index b0 j == S.index input (j + (i * Spec.size_block a)))
      end
    end;
  assert (forall (i:nat{i < n_blocks}) acc. f i acc == g i acc);
  Lib.Sequence.Lemmas.repeati_extensionality n_blocks f g s
#pop-options

val spec_is_incremental :
  a : alg ->
  p: Spec.blake2_params a ->
  last_node: bool ->
  k: lbytes (UInt8.v p.key_length) ->
  input:S.seq uint8 { if p.key_length = 0uy then S.length input <= max_input_length a else  S.length input + (Spec.size_block a) <= max_input_length a } ->
  Lemma(
    blake2_hash_incremental_s a p last_node k input == Spec.blake2 a last_node input p k)

#restart-solver
#push-options "--z3cliopt smt.arith.nl=false --z3rlimit 100"
let spec_is_incremental a p last_node k input0 =
  let kk = UInt8.v p.key_length in
  let key_block = if kk > 0 then Spec.blake2_key_block a kk k else S.empty in
  let key_block_len = S.length key_block in
  let input = Seq.append key_block input0 in
  let n_blocks, l_last = Spec.split a (S.length input) in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let s = init_s a p in
  repeati_split_at_eq a s input;
  let f = Spec.blake2_update1 a 0 input in
  let g = Spec.blake2_update1 a 0 blocks in
  let s1 = Lib.LoopCombinators.repeati n_blocks f s in
  let s2 = Lib.LoopCombinators.repeati n_blocks g s in
  assert (s1 == s2);

  S.lemma_eq_intro (S.slice input (S.length input - l_last) (S.length input)) last;
  S.lemma_eq_intro (S.slice last (S.length last - l_last) (S.length last)) last;
  Spec.Blake2.Alternative.lemma_spec_equivalence_update a last_node kk k input0 s
#pop-options

inline_for_extraction noextract
val init_key_block (a : alg) (i : index a) (k : params_and_key a i)
  (buf_: B.buffer uint8 { B.length buf_ = Spec.size_block a }) :
  ST.Stack unit
  (requires fun h0 ->
    let key = stateful_key a in
    key.invariant #i h0 k /\
    B.live h0 buf_ /\
    B.(loc_disjoint (loc_buffer buf_) (key.footprint #i h0 k)))
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer buf_) h0 h1) /\
    begin
    let _, k = (stateful_key a).v i h0 k in
    let input_length = if i.key_length <> 0uy then Spec.size_block a else 0 in
    let input = if i.key_length <> 0uy then Spec.blake2_key_block a (UInt8.v (i.key_length)) k else S.empty in
    S.equal (S.slice (B.as_seq h1 buf_) 0 input_length) input
    end)

let init_key_block a i k buf_ =
  let kk = FStar.Int.Cast.uint8_to_uint32 (i.key_length) in
  let _, k' = k in
  if kk = 0ul then ()
  else
    begin
    (**) let h0 = ST.get () in

    (* Set the end of the buffer to 0 *)
    [@inline_let] let sub_b_len = U32.(block_len a -^ kk) in
    let sub_b = B.sub buf_ kk sub_b_len in
    B.fill sub_b (Lib.IntTypes.u8 0) sub_b_len;
    (**) let h1 = ST.get () in
    (**) assert(S.slice (B.as_seq h1 buf_) (U32.v kk) (Spec.size_block a) `S.equal` B.as_seq h1 sub_b);

    (* Copy the key at the beginning of the buffer *)
    Lib.Buffer.update_sub #Lib.Buffer.MUT #uint8 #(U32.uint_to_t (Spec.size_block a)) buf_ 0ul kk k';
    (**) let h2 = ST.get () in
    (**) begin
    (**) let k : LS.lseq uint8 (U32.v kk) = snd ((stateful_key a).v i h0 k) in
    (**) let buf_v1 : LS.lseq uint8 (Spec.size_block a) = B.as_seq h1 buf_ in
    (**) let buf_v2 : LS.lseq uint8 (Spec.size_block a) = B.as_seq h2 buf_ in

    (* Prove that [buf_] is equal to [key @ create ... 0] *)
    (**) assert(buf_v2 `S.equal` LS.update_sub buf_v1 0 (U32.v kk) k);
    (**) let zeroed : LS.lseq uint8 (Spec.size_block a - (U32.v kk)) = S.create (Spec.size_block a - (U32.v kk)) (Lib.IntTypes.u8 0) in
    (**) assert(B.as_seq h1 sub_b `S.equal` zeroed);
    (**) let key_and_zeroed : LS.lseq uint8 (Spec.size_block a) = Seq.append k zeroed in
    (**) assert(S.equal (S.slice key_and_zeroed 0 (U32.v kk)) k);
    (**) assert(S.equal (S.slice key_and_zeroed (U32.v kk) (Spec.size_block a)) zeroed);
    (**) LS.lemma_update_sub #uint8 #(Spec.size_block a) buf_v1 0 (U32.v kk) k key_and_zeroed;
    (**) assert(buf_v2 `S.equal` key_and_zeroed);

    (* Prove that the initial input is equal to [key @ create ... 0] *)
    (**) let input = Spec.blake2_key_block a (U32.v kk) k in
    (**) let key_block0: LS.lseq uint8 (Spec.size_block a) = S.create (Spec.size_block a) (Lib.IntTypes.u8 0) in
    (**) assert(input `S.equal` LS.update_sub key_block0 0 (U32.v kk) k);
    (**) assert(Seq.equal (LS.sub key_and_zeroed 0 (U32.v kk)) k);
    (**) assert(Seq.equal (LS.sub key_and_zeroed (U32.v kk) (Spec.size_block a - (U32.v kk)))
                          (LS.sub key_block0 (U32.v kk) (Spec.size_block a - (U32.v kk))));
    (**) LS.lemma_update_sub #uint8 #(Spec.size_block a) key_block0 0 (U32.v kk) k key_and_zeroed;
    (**) assert(input `S.equal` key_and_zeroed)
    (**) end
    end

/// Runtime
/// -------

let _: squash (inversion Spec.alg) = allow_inversion Spec.alg

#push-options "--ifuel 2 --fuel 2 --z3rlimit 300"// --z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let blake2 (a : alg)
           (m : valid_m_spec a)
           (init : blake2_init_with_params_st a m)
           (update_multi : blake2_update_multi_st a m)
           (update_last : blake2_update_last_st a m)
           (finish : blake2_finish_st a m) :
  I.block (index a) =
  I.Block
    I.Erased (* key management *)

    (stateful_blake2 a m) (* state *)
    (stateful_key a)   (* key *)

    // Chosen once and for all, cannot be renegotiated throughout the lifetime of the state.
    unit (* output_length_t *)

    (fun _ -> max_input_len a) (* max_input_length *)
    (fun i _ -> UInt8.v (i.digest_length)) (* output_len *)
    (fun _ -> block_len a) (* block_len *)
    (fun _ -> block_len a) (* blocks_state_len *)
    (fun i -> let kk = i.key_length in if kk <> 0uy then block_len a else 0ul) (* init_input_len *)

    (fun i (_, k) ->
      let kk = i.key_length in if kk <> 0uy then Spec.blake2_key_block a (UInt8.v kk) k else S.empty) (* init_input_s *)
    (fun i (p, _k) ->
      let kk = i.key_length in kk, i.digest_length, i.last_node,  init_s a p) (* init_s *)

    (fun _ (kk, nn, last_node, acc) prevlen input -> kk, nn, last_node, update_multi_s acc prevlen input) (* update_multi_s *)
    (fun _ (kk, nn, last_node, acc) prevlen input -> kk, nn, last_node, update_last_s last_node acc prevlen input) (* update_last_s *)
    (fun i (p, _k) (kk, _, _, acc) _ ->
      finish_s #a p acc) (* finish_s *)
    (fun i k input l ->
      let p, k = k in
      spec_s a p i.last_node k input) (* spec_s *)

    (* update_multi_zero *)
    (fun _ (kk, _, _, acc) prevlen -> update_multi_zero #a acc prevlen)

    (* update_multi_associative *)
    (fun _ (kk, _, _, acc) prevlen1 prevlen2 input1 input2 ->
      update_multi_associative acc prevlen1 prevlen2 input1 input2)
    (fun i (p, k) input _ ->
      spec_is_incremental a p i.last_node k input) (* spec_is_incremental *)
    (fun _ (kk, nn, last_node, _) -> { key_length = kk; digest_length = nn; last_node }) (* index_of_state *)

    (* init *)
    (fun i k' buf_ acc ->
      let p, k = k' in
      let kk = (P.get_params p).key_length in
      let nn = (P.get_params p).digest_length in
      assert (kk == (G.reveal i).key_length);
      assert (nn == (G.reveal i).digest_length);
      let kk', nn', last_node, s = acc in
      assert (kk == kk');
      assert (nn == nn');
      let i: index a = { key_length = kk; digest_length = nn; last_node } in
      [@inline_let] let wv = get_wv #a #i #m acc in
      [@inline_let] let h = get_state_p #a #i acc in
      let h0 = ST.get () in
      assert (key_invariant h0 k');
      init_key_block a i k' buf_;
      let h1 = ST.get () in
      P.frame_invariant (B.loc_buffer buf_) p h0 h1;
      assert (key_invariant h1 k');
      let pv = P.get_params p in
      init h pv;
      let h2 = ST.get () in
      P.frame_invariant (Lib.Buffer.loc h) p h1 h2;
      assert (key_invariant h2 k')
      )

    (* update_multi *)
    (fun _ (kk, _, _, acc) prevlen blocks len ->
      let wv, hash = acc in
      let nb = len `U32.div` Core.size_block a in
      update_multi #len wv hash (blake2_prevlen a prevlen) blocks nb)

    (* update_last *)
    (fun _ (kk, _, last_node, acc) prevlen last last_len ->
      let wv, hash = acc in
      update_last #last_len wv hash last_node (blake2_prevlen a prevlen) last_len last)

    (* finish *)
    (fun _ k s dst _ ->
      // Requires fuel and ifuel. Ideally, flesh out the proof instead.
      let kk, nn, last_node, acc = s in
      let i: index a = { key_length = kk; digest_length = nn; last_node } in
      [@inline_let] let wv = get_wv #a #i #m s in
      [@inline_let] let h = get_state_p #a #i s in
      finish (FStar.Int.Cast.uint8_to_uint32 nn) dst h)
#pop-options


inline_for_extraction noextract
let blake_key a kk = I.optional_key kk I.Erased (stateful_key a)
