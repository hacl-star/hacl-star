module Hacl.Streaming.Blake2

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module F = Hacl.Streaming.Functor
module I = Hacl.Streaming.Interface
module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.Mul

module Loops = Lib.LoopCombinators

/// Opening a bunch of modules for Blake2
/// =====================================

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

module Spec = Spec.Blake2
open Hacl.Impl.Blake2.Core
module Core = Hacl.Impl.Blake2.Core
open Hacl.Impl.Blake2.Generic
module Blake2s32 = Hacl.Blake2s_32
module Blake2b32 = Hacl.Blake2b_32

/// An instance of the stateful type class for blake2
/// =================================================

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

inline_for_extraction noextract
let index = unit

inline_for_extraction noextract
let alg = Spec.alg

inline_for_extraction noextract
let m_spec = Core.m_spec

/// The stateful state: (wv, hash)
inline_for_extraction noextract
let s (a : alg) (m : m_spec) = state_p a m & state_p a m

inline_for_extraction noextract
let t (a : alg) = Spec.state a

(* In the internal state, we keep wv, the working vector. It's essentially
temporary scratch space that the Blake2 implementation expects to receive. (Why
is the implementation not performing its own stack allocations? Don't know!) *)
inline_for_extraction noextract
let get_wv (#a : alg) (#m : m_spec) (s : s a m) : Tot (state_p a m) =
  match s with wv, _ -> wv

inline_for_extraction noextract
let get_state_p (#a : alg) (#m : m_spec) (s : s a m) : Tot (state_p a m) =
  match s with _, p -> p

(* But the working vector is not reflected in the state at all -- it doesn't
have meaningful specification contents. *)
inline_for_extraction noextract
let state_v (#a : alg) (#m : m_spec) (h : HS.mem) (s : s a m) : GTot (Spec.state a) =
  Core.state_v h (get_state_p s)

inline_for_extraction noextract
let s_v (#a : alg) (#m : m_spec) (h : HS.mem) (s : s a m) : GTot (t a) =
  state_v h s

/// Small helper which facilitates inferencing implicit arguments for buffer
/// operations
inline_for_extraction noextract
let state_to_lbuffer (#a : alg) (#m : m_spec) (s : state_p a m) :
  B.lbuffer (element_t a m) (4 * U32.v (row_len a m)) =
  s

inline_for_extraction noextract
let stateful_blake2 (a : alg) (m : m_spec) : I.stateful unit =
  I.Stateful
    (fun () -> s a m) (* s *)
    (* footprint *)
    (fun #_ _ acc ->
      let wv, b = acc in
      B.loc_union
       (B.loc_addr_of_buffer (state_to_lbuffer wv))
       (B.loc_addr_of_buffer (state_to_lbuffer b)))
    (* freeable *)
    (fun #_ _ acc ->
      let wv, b = acc in
      B.freeable (state_to_lbuffer wv) /\
      B.freeable (state_to_lbuffer b))
    (* invariant *)
    (fun #_ h acc ->
      let wv, b = acc in
      B.live h (state_to_lbuffer wv) /\
      B.live h (state_to_lbuffer b) /\
      B.disjoint (state_to_lbuffer wv) (state_to_lbuffer b))
    (fun () -> t a) (* t *)
    (fun () h acc -> s_v h acc) (* v *)
    (fun #_ h acc -> let wv, b = acc in ()) (* invariant_loc_in_footprint *)
    (fun #_ l acc h0 h1 -> let wv, b = acc in ()) (* frame_invariant *)
    (fun #_ _ _ _ _ -> ()) (* frame_freeable *)
    (* alloca *)
    (fun () ->
      let wv = alloc_state a m in
      let b = alloc_state a m in
      wv, b)
    (* create_in *)
    (fun () r ->
      let wv = B.malloc r (zero_element a m) U32.(4ul *^ row_len a m) in
      let b = B.malloc r (zero_element a m) U32.(4ul *^ row_len a m) in
      wv, b)
    (* free *)
    (fun _ acc ->
      match acc with wv, b ->
      B.free (state_to_lbuffer wv);
      B.free (state_to_lbuffer b))
    (* copy *)
    (fun _ src dst ->
      match src with src_wv, src_b ->
      match dst with src_wv, dst_b ->
      B.blit (state_to_lbuffer src_b) 0ul (state_to_lbuffer dst_b) 0ul
             U32.(4ul *^ row_len a m))

/// Stateful key
/// ============

inline_for_extraction noextract
let key_size_ty (a : alg) = key_size:nat{0 <= key_size /\ key_size <= Spec.max_key a}

inline_for_extraction noextract
let key_size_t (a : alg) (is_zero: bool) =
  key_size:U32.t{
    0 <= U32.v key_size /\ U32.v key_size <= Spec.max_key a /\
    (is_zero ==> U32.v key_size = 0)}

/// Defining stateful keys
inline_for_extraction noextract
let stateful_key_t (a : alg) (no_key : bool)
                   (key_size : key_size_t a no_key) : Type =
  if no_key then unit else b:B.buffer uint8 { B.length b == U32.v key_size}

inline_for_extraction noextract
let buffer_to_stateful_key_t (a : alg) (key_size : key_size_t a false)
                             (k : B.buffer uint8 { B.length k == U32.v key_size }) :
  Tot (stateful_key_t a false key_size) =
  k

inline_for_extraction noextract
let unit_to_stateful_key_t (a : alg) :
  Tot (stateful_key_t a true 0ul) =
  ()

/// The ``has_key`` parameter is meta
/// TODO: this definition could be moved to Hacl.Streaming.Interface, it could
/// be pretty useful in other situations as it generalizes ``stateful_buffer`` in
/// the case the length is zero. Note that rather than being unit, the type could
/// be buffer too (and we would use null whenever needed).
inline_for_extraction noextract
let stateful_key (a : alg) (no_key : bool) (key_size : key_size_t a no_key) :
  I.stateful unit =
  I.Stateful
    (fun _ -> stateful_key_t a no_key key_size)
    (* footprint *)
    (fun #_ h s -> if U32.v key_size = 0 then B.loc_none else B.loc_addr_of_buffer (s <: B.buffer uint8))
    (* freeable *)
    (fun #_ h s -> if U32.v key_size = 0 then True else B.freeable (s <: B.buffer uint8))
    (* invariant *)
    (fun #_ h s ->
      if no_key then True else if U32.v key_size = 0 then (s <: B.buffer uint8) == B.null
      else B.live h (s <: B.buffer uint8))
    (fun _ -> s:S.seq uint8 { S.length s == U32.v key_size })
    (fun _ h s -> if U32.v key_size = 0 then Seq.empty else B.as_seq h (s <: B.buffer uint8))
    (fun #_ h s -> ()) (* invariant_loc_in_footprint *)
    (fun #_ l s h0 h1 -> ()) (* frame_invariant *)
    (fun #_ l s h0 h1 -> ()) (* frame_freeable *)

    (* alloca *)
    (fun () ->
       if no_key then unit_to_stateful_key_t a
       else if U32.(key_size >^ 0ul) then
         buffer_to_stateful_key_t a key_size (B.alloca (Lib.IntTypes.u8 0) key_size)
       else buffer_to_stateful_key_t a key_size B.null)

    (* create_in *)
    (fun () r ->
       if no_key then unit_to_stateful_key_t a
       else if U32.(key_size >^ 0ul) then
         buffer_to_stateful_key_t a key_size (B.malloc r (Lib.IntTypes.u8 0) key_size)
       else buffer_to_stateful_key_t a key_size B.null)

    (* free *)
    (fun _ s ->
      if no_key then ()
      else if U32.(key_size >^ 0ul) then B.free (s <: B.buffer uint8) else ())

    (* copy *)
    (fun _ s_src s_dst ->
      if no_key then ()
      else
        if U32.(key_size >^ 0ul) then
          B.blit (s_src <: B.buffer uint8) 0ul
                 (s_dst <: B.buffer uint8) 0ul key_size
        else ())

inline_for_extraction noextract
let stateful_key_to_buffer (#a : alg) (#no_key : bool) (#key_size : key_size_t a no_key)
                           (key : stateful_key_t a no_key key_size) :
  b:B.buffer uint8 { B.length b = U32.v key_size } =
  if no_key then B.null #uint8 else key

inline_for_extraction noextract
let k = stateful_key

/// Actual functor instantiation
/// ============================

/// Small helpers
/// -------------

noextract
let max_input_length (a : alg) : n:nat { n <= Spec.max_limb a } =
  assert_norm (pow2 64 < pow2 128);
  pow2 64 - 1

noextract inline_for_extraction
let max_input_len (a: alg): (x:U64.t { U64.v x == max_input_length a }) = 0xffffffffffffffffUL

inline_for_extraction noextract
let block (a : alg) = (block: S.seq uint8 { S.length block = Spec.size_block a })

inline_for_extraction noextract
let block_len (a : alg) : U32.t = Core.size_block a

inline_for_extraction noextract
let output_size (a : alg) : nat = Spec.max_output a

inline_for_extraction noextract
let output_len (a : alg) = U32.uint_to_t (output_size a)

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
let init_s (a : alg) :
  Tot (t a) =
  Spec.blake2_init_hash a 0 (output_size a)

noextract
let update_multi_s (#a : alg) (acc : t a)
                   (prevlen : nat{prevlen % Spec.size_block a = 0})
                   (input : Seq.seq uint8{ prevlen + S.length input <= max_input_length a /\
                                           S.length input % Spec.size_block a = 0 }) :
  Tot (t a)
=
  let nb = S.length input / U32.v (block_len a) in
  Lib.LoopCombinators.repeati nb (Spec.blake2_update1 a prevlen input) acc

noextract
let update_last_s (#a : alg) (acc : t a)
                  (prevlen : nat{prevlen % Spec.size_block a = 0})
                  (input : Seq.seq uint8{ S.length input + prevlen <= max_input_length a /\
                                          S.length input <= Spec.size_block a }) :
  Tot (t a) =
  Spec.blake2_update_last a prevlen (S.length input) input acc

noextract
let finish_s (#a : alg) (acc : t a) :
  output : S.seq uint8 { S.length output = U32.v (output_len a) } =
  Spec.blake2_finish a acc (U32.v (output_len a))

noextract
let spec_s (a : alg) (_key : unit)
           (input : S.seq uint8{S.length input <= max_input_length a}) =
  Spec.blake2 a input 0 Seq.empty (output_size a)

/// Interlude for spec proofs
/// -------------------------

val update_multi_zero:
  #a : alg ->
  acc:t a ->
  prevlen:nat{prevlen % Spec.size_block a = 0} ->
  Lemma
  (requires (prevlen <= max_input_length a))
  (ensures (update_multi_s #a acc prevlen S.empty == acc))

let update_multi_zero #a acc prevlen =
  Lib.LoopCombinators.eq_repeati0 (0 / U32.v (block_len a)) (Spec.blake2_update1 a prevlen S.empty) acc

val update_multi_associative:
  #a : alg ->
  acc: t a ->
  prevlen1:nat ->
  prevlen2:nat ->
  input1:S.seq uint8 ->
  input2:S.seq uint8 ->
  Lemma
  (requires (
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

let update_multi_associative #a acc prevlen1 prevlen2 input1 input2 =
  let input = S.append input1 input2 in
  let nb = S.length input / U32.v (block_len a) in
  let f = Spec.blake2_update1 a prevlen1 input in
  (* calc (==) {
    update_multi_s () acc prevlen1 input;
  (==) { }
    Lib.LoopCombinators.repeati nb (Spec.blake2_update1 a prevlen1 input) acc;
  (==) { }
    Lib.LoopCombinators.repeati nb f acc;
  (==) { Lib.Sequence.Lemmas.repeati_extensionality }
    Lib.LoopCombinators.repeati nb (Lib.Sequence.repeat_blocks_f (U32.v (block_len a)) input f nb) acc;
  (==) { Lib.Sequence.lemma_repeat_blocks_multi ... }
    Lib.LoopCombinators.repeat_blocks_multi ...
  (==) { Lib.Sequence.Lemmas.repeat_blocks_multi_split ... }
    Lib.LoopCombinators.(repeat_blocks_multi ... (repeat_blocks_multi ...))
  ... inverse direction ...
  }; *)
  admit ()

/// A helper function: the hash incremental function defined with the functions
/// locally defined (with a signature adapted to the functor).
noextract
val blake2_hash_incremental_s :
  a : alg ->
  input:S.seq uint8 { S.length input <= max_input_length a} ->
  output:S.seq uint8 { S.length output = output_size a }

#push-options "--z3cliopt smt.arith.nl=false"
let blake2_hash_incremental_s a input =
  (**) Math.Lemmas.modulo_lemma 0 (U32.v (block_len a));
  let bs, l = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let acc1 = init_s a in
  let acc2 = update_multi_s #a acc1 0 bs in
  let acc3 = update_last_s #a acc2 (S.length bs) l in
  let acc4 = finish_s #a acc3 in
  acc4
#pop-options

val spec_is_incremental :
  a : alg ->
  input:S.seq uint8 { S.length input <= max_input_length a } ->
  Lemma(
    blake2_hash_incremental_s a input ==
      Spec.blake2 a input 0 S.empty (output_size a))

let spec_is_incremental a input =
  let n_blocks, l_last = Spec.split a (S.length input) in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let s = init_s a in
  let s1 = Lib.LoopCombinators.repeati n_blocks (Spec.blake2_update1 a 0 input) s in
  let s2 = Lib.LoopCombinators.repeati n_blocks (Spec.blake2_update1 a 0 blocks) s in
  Lib.Sequence.Lemmas.repeati_extensionality n_blocks (Spec.blake2_update1 a 0 input)
    (Spec.blake2_update1 a 0 blocks) s;
  S.lemma_eq_intro (S.slice input (S.length input - l_last) (S.length input)) last;
  S.lemma_eq_intro (S.slice last (S.length last - l_last) (S.length last)) last

/// Runtime
/// -------

let blocks_state_len (a : alg) (m : valid_m_spec a) :
  Tot (x:U32.t{
    U32.v x > 0 /\
    U32.v x % U32.v (block_len a) = 0
  }) = 
  match m with
  | M32 -> block_len a
  // The vectorized implementations actually only process one block at a time
  | M128 -> block_len a
  | M256 -> block_len a

#push-options "--ifuel 1"// --z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let blake2 (a : alg) (m : valid_m_spec a)
           (init : blake2_init_st a m)
           (update_multi : blake2_update_multi_st a m)
           (update_last : blake2_update_last_st a m)
           (finish : blake2_finish_st a m) :
  I.block unit =
  I.Block
    I.Erased (* key management *)

    (stateful_blake2 a m)     (* state *)
    (I.stateful_unused unit)  (* key *)

    (fun () -> max_input_len a ) (* max_input_length *)
    (fun () -> output_len a) (* output_len *)
    (fun () -> block_len a) (* block_len *)
    (fun () -> blocks_state_len a m) (* blocks_state_len *)

    (fun () _k -> init_s a) (* init_s *)
    (fun () acc prevlen input -> update_multi_s acc prevlen input) (* update_multi_s *)
    (fun () acc prevlen input -> update_last_s acc prevlen input) (* update_last_s *)
    (fun () _k acc -> finish_s #a acc) (* finish_s *)
    (fun () -> spec_s a) (* spec_s *)

    (* update_multi_zero *)
    (fun () prevlen acc -> update_multi_zero prevlen acc)
    (* update_multi_associative *)
    (fun () acc prevlen1 prevlen2 input1 input2 ->
      update_multi_associative acc prevlen1 prevlen2 input1 input2)
    (fun () _k input -> spec_is_incremental a input) (* spec_is_incremental *)
    (fun _ acc -> ()) (* index_of_state *)

    (* init *)
    (fun _ key acc ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      init h (Lib.IntTypes.size 0) (output_len a))

    (* update_multi *)
    (fun _ acc prevlen blocks len ->
      let wv, hash = acc in
      let nb = len `U32.div` size_block a in
      blake2_update_multi #a #m blake2_update_block #len wv hash (blake2_prevlen a prevlen) blocks nb)

    (* update_last *)
    (fun _ acc prevlen last last_len ->
      let wv, hash = acc in
      blake2_update_last #a #m blake2_update_block #last_len wv hash (blake2_prevlen a prevlen) last_len last)

    (* finish *)
    (fun _ k acc dst ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      finish (output_len a) dst h)
#pop-options

/// Introducing intermediate definitions for the instantiation

inline_for_extraction noextract
let blake2s_32 =
  blake2 Spec.Blake2S M32 Blake2s32.blake2s_init Blake2s32.blake2s_update_multi
         Blake2s32.blake2s_update_last Blake2s32.blake2s_finish

inline_for_extraction noextract
let blake2b_32 =
  blake2 Spec.Blake2B M32 Blake2b32.blake2b_init Blake2b32.blake2b_update_multi
         Blake2b32.blake2b_update_last Blake2b32.blake2b_finish

/// We don't use a key for streaming blake2: it is thus the unit typeclass
inline_for_extraction noextract
let unit_key = I.optional_key () I.Erased (I.stateful_unused unit)

/// Type abbreviations - makes KaRaMeL use pretty names in the generated code

let blake2s_32_block_state = s Spec.Blake2S M32
let blake2b_32_block_state = s Spec.Blake2B M32
let blake2s_32_state = F.state_s blake2s_32 () (s Spec.Blake2S M32) unit_key
let blake2b_32_state = F.state_s blake2b_32 () (s Spec.Blake2B M32) unit_key

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
let blake2s_32_no_key_alloca =
  F.alloca blake2s_32 () (s Spec.Blake2S M32) unit_key

[@ (Comment "  State allocation function when there is no key")]
let blake2s_32_no_key_create_in =
  F.create_in blake2s_32 () (s Spec.Blake2S M32) unit_key

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2s_32_no_key_init =
  F.init blake2s_32 () (s Spec.Blake2S M32) unit_key

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2s_32_no_key_update =
  F.update blake2s_32 (G.hide ()) (s Spec.Blake2S M32) unit_key

[@ (Comment "  Finish function when there is no key")]
let blake2s_32_no_key_finish =
  F.mk_finish blake2s_32 () (s Spec.Blake2S M32) unit_key

[@ (Comment "  Free state function when there is no key")]
let blake2s_32_no_key_free =
  F.free blake2s_32 (G.hide ()) (s Spec.Blake2S M32) unit_key

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let blake2b_32_no_key_alloca =
  F.alloca blake2b_32 () (s Spec.Blake2B M32) unit_key

[@ (Comment "  State allocation function when there is no key")]
let blake2b_32_no_key_create_in =
  F.create_in blake2b_32 () (s Spec.Blake2B M32) unit_key

[@ (Comment "  (Re)-initialization function when there is no key")]
let blake2b_32_no_key_init =
  F.init blake2b_32 () (s Spec.Blake2B M32) unit_key

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2b_32_no_key_update =
  F.update blake2b_32 (G.hide ()) (s Spec.Blake2B M32) unit_key

[@ (Comment "  Finish function when there is no key")]
let blake2b_32_no_key_finish =
  F.mk_finish blake2b_32 () (s Spec.Blake2B M32) unit_key

[@ (Comment "  Free state function when there is no key")]
let blake2b_32_no_key_free =
  F.free blake2b_32 (G.hide ()) (s Spec.Blake2B M32) unit_key
