module Hacl.Streaming.Blake2s_32

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Case = FStar.Int.Cast.Full
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module P = Hacl.Impl.Poly1305
module ST = FStar.HyperStack.ST

module Agile = Spec.Agile.Hash
module Hash = Spec.Hash.Definitions

open LowStar.BufferOps
open FStar.Mul

/// Opening a bunch of modules for Blake2
/// =======================================

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
module Core = Hacl.Impl.Blake2.Core
open Hacl.Impl.Blake2.Generic
module Impl = Hacl.Impl.Blake2.Generic
module Incr = Spec.Hash.Incremental

//open Hacl.Blake2s_32

/// An instance of the stateful type class for blake2
/// =========================================================

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

inline_for_extraction noextract
let a = Spec.Blake2S

inline_for_extraction noextract
let m = M32

let to_hash_alg (a : Spec.alg) =
  match a with
  | Spec.Blake2S -> Hash.Blake2S
  | Spec.Blake2B -> Hash.Blake2B

let index = unit

/// The stateful state: (wv, hash, *total_len)
/// The total_len pointer should actually be ghost
inline_for_extraction noextract
let s = state_p a m & state_p a m & B.pointer (Hash.extra_state (to_hash_alg a))

inline_for_extraction noextract
let extra_state_zero_element a : Hash.extra_state (to_hash_alg a) =
  Hash.nat_to_extra_state (to_hash_alg a) 0

inline_for_extraction noextract
let t = Hash.words_state (to_hash_alg a)

inline_for_extraction noextract
let get_wv (s : s) : Tot (state_p a m) =
  match s with wv, _, _ -> wv

inline_for_extraction noextract
let get_state_p (s : s) : Tot (state_p a m) =
  match s with _, p, _ -> p

inline_for_extraction noextract
let state_v (h : HS.mem) (s : s) : GTot (Spec.state a) =
  Core.state_v h (get_state_p s)

inline_for_extraction noextract
let get_extra_state_p (s : s) : Tot (B.pointer (Hash.extra_state (to_hash_alg a))) =
  match s with _, _, l -> l

inline_for_extraction noextract
let extra_state_v (h : HS.mem) (s : s) : GTot (Hash.extra_state (to_hash_alg a))=
  B.deref h (get_extra_state_p s)

inline_for_extraction noextract
let s_v (h : HS.mem) (s : s) : GTot t = state_v h s, extra_state_v h s

/// Small helper which facilitates inferencing implicit arguments for buffer
/// operations
inline_for_extraction noextract
let state_to_lbuffer (s : state_p a m) :
  B.lbuffer (element_t a m) (4 * U32.v (row_len a m)) =
  s

inline_for_extraction noextract
let stateful_blake2s_32: I.stateful unit =
  I.Stateful
    (fun () -> s) (* s *)
    (* footprint *)
    (fun #_ _ acc ->
      let wv, b, l = acc in
      B.loc_union
        (B.loc_union
          (B.loc_addr_of_buffer (state_to_lbuffer wv))
          (B.loc_addr_of_buffer (state_to_lbuffer b)))
        (B.loc_addr_of_buffer l))
    (* freeable *)
    (fun #_ _ acc ->
      let wv, b, l = acc in
      B.freeable (state_to_lbuffer wv) /\
      B.freeable (state_to_lbuffer b) /\
      B.freeable l)
    (* invariant *)
    (fun #_ h acc ->
      let wv, b, l = acc in
      B.live h (state_to_lbuffer wv) /\
      B.live h (state_to_lbuffer b) /\
      B.live h l /\
      B.disjoint (state_to_lbuffer wv) (state_to_lbuffer b) /\
      B.disjoint (state_to_lbuffer wv) l /\
      B.disjoint (state_to_lbuffer b) l)
    (fun () -> t) (* t *)
    (fun () h acc -> s_v h acc) (* v *)
    (fun #_ h acc -> let wv, b, l = acc in ()) (* invariant_loc_in_footprint *)
    (fun #_ l acc h0 h1 -> let wv, b, l = acc in ()) (* frame_invariant *)
    (fun #_ _ _ _ _ -> ()) (* frame_freeable *)
    (* alloca *)
    (fun () ->
      let wv = alloc_state a m in
      let b = alloc_state a m in
      let l = B.alloca (extra_state_zero_element a) (U32.uint_to_t 1) in
      wv, b, l)
    (* create_in *)
    (fun () r ->
      let wv = B.malloc r (zero_element a m) U32.(4ul *^ row_len a m) in
      let b = B.malloc r (zero_element a m) U32.(4ul *^ row_len a m) in
      let l = B.malloc r (extra_state_zero_element a) (U32.uint_to_t 1) in
      wv, b, l)
    (* free *)
    (fun _ acc ->
      match acc with wv, b, l ->
      B.free (state_to_lbuffer wv);
      B.free (state_to_lbuffer b);
      B.free l)
    (* copy *)
    (fun _ src dst ->
      match src with src_wv, src_b, src_l ->
      match dst with src_wv, dst_b, dst_l ->
      B.blit (state_to_lbuffer src_b) 0ul (state_to_lbuffer dst_b) 0ul
             U32.(4ul *^ row_len a m);
      B.blit src_l 0ul dst_l 0ul 1ul)

inline_for_extraction noextract
let k (key_size : nat{0 < key_size /\ key_size <= Spec.max_key a}) =
  I.stateful_buffer uint8 (U32.uint_to_t key_size) (Lib.IntTypes.u8 0)

let max_input_length (key_size : nat) : nat =
  if key_size = 0 then Spec.max_limb a
  else Spec.max_limb a - Spec.size_block a

inline_for_extraction noextract
let block = (block: S.seq uint8 { S.length block = Spec.size_block a })

inline_for_extraction noextract
let block_len = Core.size_block a

inline_for_extraction noextract
let key_size : nat = Spec.max_key a

inline_for_extraction noextract
let key_len : U32.t = U32.uint_to_t key_size

inline_for_extraction noextract
let output_size : nat = Spec.max_output a

inline_for_extraction noextract
let output_len = U32.uint_to_t output_size

let init_s () key : Hash.words_state (to_hash_alg a) =
  Spec.blake2_init a key_size key output_size,
  Hash.nat_to_extra_state (to_hash_alg a) (Spec.compute_prev0 a key_size)
  //extra_state_zero_element a
let update_s () acc = Agile.update (to_hash_alg a)
let update_multi_s () = Agile.update_multi (to_hash_alg a)
let update_last_s () = Spec.Hash.Incremental.update_last (to_hash_alg a)
let finish_s () = Spec.Hash.PadFinish.finish (to_hash_alg a)

let spec_s ()
           (key : S.seq uint8{S.length key = key_size})
           (input : S.seq uint8{S.length input <= max_input_length key_size}) = 
  Spec.blake2 a input key_size key output_size

/// Interlude for spec proofs
/// =====================================
val update_multi_zero:
  i:index ->
  acc:t ->
  Lemma
  (ensures (update_multi_s i acc S.empty == acc))

let update_multi_zero () acc =
  Spec.Hash.Lemmas.update_multi_zero (to_hash_alg a) acc

val  update_multi_associative:
  i:index ->
  acc: t ->
  input1:S.seq uint8 ->
  input2:S.seq uint8 ->
  Lemma
  (requires (
    S.length input1 % U32.v block_len = 0 /\
    S.length input2 % U32.v block_len = 0))
  (ensures (
    let input = S.append input1 input2 in
    S.length input % U32.v block_len = 0 /\
    update_multi_s i (update_multi_s i acc input1) input2 ==
      update_multi_s i acc input))

let update_multi_associative () acc input1 input2 =
  Spec.Hash.Lemmas.update_multi_associative (to_hash_alg a) acc input1 input2

val spec_is_incremental:
  i:index ->
  key: I.((k key_size).t ()) ->
  input:S.seq uint8 { S.length input <= max_input_length key_size } ->
  Lemma (ensures (
    let open FStar.Mul in
    let block_length = U32.v block_len in
    let n = S.length input / block_length in
    let rem = S.length input % block_length in (**)
    let n, rem = if rem = 0 && n > 0 then n - 1, block_length else n, rem in (**)
    let bs, l = S.split input (n * block_length) in
    (**) FStar.Math.Lemmas.multiple_modulo_lemma n block_length;
    let hash = update_multi_s i (init_s i key) bs in
    let hash = update_last_s i hash (n * block_length) l in
    finish_s i hash `S.equal` spec_s i key input))

let spec_is_incremental () key input =
  Spec.Hash.Incremental.blake2_is_hash_incremental (to_hash_alg a) key_size key input

#push-options "--ifuel 1"
inline_for_extraction noextract
let blake2s_32 : I.block unit =
  I.Block
    I.Erased (* key management *)
    
    stateful_blake2s_32 (* state *)
    (k key_size) (* key *)
    
    (fun () -> max_input_length (Spec.max_key a)) (* max_input_length *)
    (fun () -> output_len) (* output_len *)
    (fun () -> block_len) (* block_len *)
    
    (fun () k -> init_s () k) (* init_s *)
    (fun () acc input -> update_multi_s () acc input) (* update_multi_s *)
    (fun () acc prevlen input -> update_last_s () acc prevlen input) (* update_last_s *)
    (fun () k acc -> finish_s () acc) (* finish_s *)
    (fun () -> spec_s ()) (* spec_s *)

    (fun () acc -> update_multi_zero () acc) (* update_multi_zero *)
    (fun () acc input1 input2 -> update_multi_associative () acc input1 input2) (* update_multi_associative *)
    (fun () k input -> spec_is_incremental () k input) (* spec_is_incremental *)
    (fun _ acc -> ()) (* index_of_state *)

    (* init *)
    (fun _ key acc ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      [@inline_let] let es = get_extra_state_p acc in
      Impl.blake2_init #a #m (Impl.blake2_update_block #a #m) wv h key_len key output_len;
      B.upd es 0ul (extra_state_zero_element a))
    (fun _ -> admit()) (* update_multi *)
    (* update_last *)
    (fun _ acc prev_len last last_len ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      [@inline_let] let es = get_extra_state_p acc in
      (**) let h0 = ST.get () in
      assert_norm(U64.v prev_len + U32.v last_len <= Spec.Blake2.max_limb a);
      [@inline_let]
      let prev_len' : Spec.Blake2.limb_t a =
        match a with
        | Spec.Blake2S -> Lib.IntTypes.(cast #U64 #PUB U64 SEC prev_len)
        | Spec.Blake2B -> FStar.Int.Cast.Full.uint64_to_uint128 prev_len
      in
      Impl.blake2_update_last #a #m (Impl.blake2_update_block #a #m) #last_len
                              wv h
                              prev_len' last_len last;
      B.upd es 0ul (extra_state_zero_element a);
      (**) let h2 = ST.get () in
      assert(
        Core.state_v h2 h ==
          Spec.blake2_update_last a (U64.v prev_len) (U32.v last_len) (B.as_seq h0 last)
                                  (Core.state_v h0 h));
      assume(s_v h2 acc ==
             update_last_s () (s_v h0 acc) (U64.v prev_len) (B.as_seq h0 last))
      )

    (* finish *)
    (fun _ k acc dst ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
//      [@inline_let] let es = get_extra_state_p acc in
      Impl.blake2_finish #a #m output_len dst h)
#pop-options

/// The incremental hash functions instantiations
let create_in = F.create_in blake2s_32 () s (I.optional_key () I.Erased (k key_size))
let init = F.init blake2s_32 (G.hide ()) s (I.optional_key () I.Erased (k key_size))
let update = F.update blake2s_32 (G.hide ()) s (I.optional_key () I.Erased (k key_size))
let finish = F.mk_finish blake2s_32 () s (I.optional_key () I.Erased (k key_size))
let free = F.free blake2s_32 (G.hide ()) s (I.optional_key () I.Erased (k key_size))
