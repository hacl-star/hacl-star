module Hacl.Streaming.Blake2

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module LS = Lib.Sequence
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module F = Hacl.Streaming.Functor
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
open Hacl.Impl.Blake2.Generic
module Blake2s32 = Hacl.Blake2s_32
module Blake2b32 = Hacl.Blake2b_32

/// An instance of the stateful type class for blake2
/// =================================================

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

inline_for_extraction noextract
let index = unit

inline_for_extraction noextract
let alg = Spec.alg

inline_for_extraction noextract
let m_spec = Core.m_spec

/// The stateful state: (wv, hash)
inline_for_extraction noextract
let s (a : alg) (m : m_spec) = Core.(state_p a m & state_p a m)

inline_for_extraction noextract
let t (a : alg) = Spec.state a

(* In the internal state, we keep wv, the working vector. It's essentially
temporary scratch space that the Blake2 implementation expects to receive. (Why
is the implementation not performing its own stack allocations? Don't know!) *)
inline_for_extraction noextract
let get_wv (#a : alg) (#m : m_spec) (s : s a m) : Tot (Core.state_p a m) =
  match s with wv, _ -> wv

inline_for_extraction noextract
let get_state_p (#a : alg) (#m : m_spec) (s : s a m) : Tot (Core.state_p a m) =
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
let state_to_lbuffer (#a : alg) (#m : m_spec) (s : Core.state_p a m) :
  B.lbuffer (Core.element_t a m) (4 * U32.v (Core.row_len a m)) =
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
      let wv = Core.alloc_state a m in
      let b = Core.alloc_state a m in
      wv, b)
    (* create_in *)
    (fun () r ->
      let wv = B.malloc r (Core.zero_element a m) U32.(4ul *^ Core.row_len a m) in
      let b = B.malloc r (Core.zero_element a m) U32.(4ul *^ Core.row_len a m) in
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
             U32.(4ul *^ Core.row_len a m))

/// Stateful key
/// ============

inline_for_extraction noextract
let key_size (a : alg) = kk:nat{kk <= Spec.max_key a}

inline_for_extraction noextract
let key_size_t (a : alg) =
  key_size:U32.t{U32.v key_size <= Spec.max_key a}

/// Defining stateful keys
inline_for_extraction noextract
let stateful_key_t (a : alg) (key_size : key_size a) : Type =
  if key_size = 0 then unit else b:B.buffer uint8 { B.length b == key_size}

inline_for_extraction noextract
let buffer_to_stateful_key_t (a : alg) (kk : key_size a{kk > 0})
                             (k : B.buffer uint8 { B.length k == kk }) :
  Tot (stateful_key_t a kk) =
  k

inline_for_extraction noextract
let unit_to_stateful_key_t (a : alg) :
  Tot (stateful_key_t a 0) =
  ()

/// The ``has_key`` parameter is meta
/// TODO: this definition could be moved to Hacl.Streaming.Interface, it could
/// be pretty useful in other situations as it generalizes ``stateful_buffer`` in
/// the case the length is zero. Note that rather than being unit, the type could
/// be buffer too (and we would use null whenever needed).
inline_for_extraction noextract
let stateful_key (a : alg) (kk : key_size a) :
  I.stateful unit =
  I.Stateful
    (fun _ -> stateful_key_t a kk)
    (* footprint *)
    (fun #_ h s -> if kk = 0 then B.loc_none else B.loc_addr_of_buffer (s <: B.buffer uint8))
    (* freeable *)
    (fun #_ h s -> if kk = 0 then True else B.freeable (s <: B.buffer uint8))
    (* invariant *)
    (fun #_ h s ->
      if kk = 0 then True
      else B.live h (s <: B.buffer uint8))
    (fun _ -> s:S.seq uint8 { S.length s == kk })
    (fun _ h s -> if kk = 0 then Seq.empty else B.as_seq h (s <: B.buffer uint8))
    (fun #_ h s -> ()) (* invariant_loc_in_footprint *)
    (fun #_ l s h0 h1 -> ()) (* frame_invariant *)
    (fun #_ l s h0 h1 -> ()) (* frame_freeable *)

    (* alloca *)
    (fun () ->
       if kk > 0 then
         buffer_to_stateful_key_t a kk (B.alloca (Lib.IntTypes.u8 0) (U32.uint_to_t kk))
       else unit_to_stateful_key_t a)

    (* create_in *)
    (fun () r ->
       if kk > 0 then
         buffer_to_stateful_key_t a kk (B.malloc r (Lib.IntTypes.u8 0) (U32.uint_to_t kk))
       else unit_to_stateful_key_t a)

    (* free *)
    (fun _ s -> if kk > 0 then B.free (s <: B.buffer uint8) else ())

    (* copy *)
    (fun _ s_src s_dst ->
      if kk > 0 then
        B.blit (s_src <: B.buffer uint8) 0ul
               (s_dst <: B.buffer uint8) 0ul (U32.uint_to_t kk)
      else ())

inline_for_extraction noextract
let stateful_key_to_buffer (#a : alg) (#kk : key_size a)
                           (key : stateful_key_t a kk) :
  b:B.buffer uint8 { B.length b = kk } =
  if kk = 0 then B.null #uint8 else key

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
let init_s (a : alg) (kk : size_nat{kk <= max_key a}) :
  Tot (t a) =
  Spec.blake2_init_hash a kk (output_size a)

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
let spec_s (a : alg)
  (kk : size_nat{kk <= max_key a})
  (key : lbytes kk)
  (input : S.seq uint8{if kk = 0 then S.length input <= max_input_length a else S.length input + Spec.size_block a <= max_input_length a}) =
  Spec.blake2 a input kk key (output_size a)

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

#push-options "--z3cliopt smt.arith.nl=false"
val update_multi_associative:
  #a : alg ->
  acc: t a ->
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
  let aux1 (i:nat{i < nb1}) (acc:t a) : Lemma (f i acc == f1 i acc)
    = assert (Spec.get_blocki a input i `Seq.equal` Spec.get_blocki a input1 i)
  in
  let aux2 (i:nat{i < nb2}) (acc:t a) : Lemma (f2 i acc == f (i + nb1) acc)
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
      repeati_def nb2 f2 (repeat_right 0 nb1 (fixed_a (t a)) f acc)
    }
    repeat_right 0 nb2 (fixed_a (t a)) f2 (repeat_right 0 nb1 (fixed_a (t a)) f acc);
    (==) {
      Classical.forall_intro_2 aux2;
      repeat_gen_right_extensionality nb2 nb1 (fixed_a (t a)) (fixed_a (t a)) f2 f (repeat_right 0 nb1 (fixed_a (t a)) f acc)
    }
    repeat_right nb1 (nb1 + nb2) (fixed_a (t a)) f (repeat_right 0 nb1 (fixed_a (t a)) f acc);
    (==) { repeat_right_plus 0 nb1 nb (fixed_a (t a)) f acc; repeati_def nb f acc }
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
  kk: size_nat{kk <= max_key a} ->
  k: lbytes kk ->
  input:S.seq uint8 { if kk = 0 then S.length input <= max_input_length a else S.length input + (Spec.size_block a) <= max_input_length a } ->
  output:S.seq uint8 { S.length output = output_size a }

#push-options "--z3cliopt smt.arith.nl=false"
let blake2_hash_incremental_s a kk k input0 =
  let key_block = if kk > 0 then Spec.blake2_key_block a kk k else S.empty in
  let key_block_len = S.length key_block in
  let input = Seq.append key_block input0 in
  assert (key_block_len = (if kk = 0 then 0 else Spec.size_block a));
  (**) Math.Lemmas.modulo_lemma 0 (U32.v (block_len a));
  let bs, l = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let acc1 = init_s a kk in
  let acc2 = update_multi_s #a acc1 0 bs in
  let acc3 = update_last_s #a acc2 (S.length bs) l in
  let acc4 = finish_s #a acc3 in
  acc4
#pop-options

#push-options "--z3cliopt smt.arith.nl=false"
val repeati_split_at_eq :
  a : alg ->
  s : t a ->
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
  kk: size_nat{kk <= max_key a} ->
  k: lbytes kk ->
  input:S.seq uint8 { if kk = 0 then S.length input <= max_input_length a else  S.length input + (Spec.size_block a) <= max_input_length a } ->
  Lemma(
    blake2_hash_incremental_s a kk k input ==
      Spec.blake2 a input kk k (output_size a))

#restart-solver
#push-options "--z3cliopt smt.arith.nl=false"
let spec_is_incremental a kk k input0 =
  let key_block = if kk > 0 then Spec.blake2_key_block a kk k else S.empty in
  let key_block_len = S.length key_block in
  let input = Seq.append key_block input0 in
  let n_blocks, l_last = Spec.split a (S.length input) in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  let s = init_s a kk in
  repeati_split_at_eq a s input;
  let f = Spec.blake2_update1 a 0 input in
  let g = Spec.blake2_update1 a 0 blocks in
  let s1 = Lib.LoopCombinators.repeati n_blocks f s in
  let s2 = Lib.LoopCombinators.repeati n_blocks g s in
  assert (s1 == s2);

  S.lemma_eq_intro (S.slice input (S.length input - l_last) (S.length input)) last;
  S.lemma_eq_intro (S.slice last (S.length last - l_last) (S.length last)) last;
  Spec.Blake2.Alternative.lemma_spec_equivalence_update a kk k input0 s;
  assert (U32.v (output_len a) = output_size a)
#pop-options

inline_for_extraction noextract
val init_key_block (a : alg) (kk : key_size a) (k : stateful_key_t a kk)
  (buf_: B.buffer uint8 { B.length buf_ = Spec.size_block a }) :
  ST.Stack unit
  (requires fun h0 ->
    let key = stateful_key a kk in
    key.invariant h0 k /\
    B.live h0 buf_ /\
    B.(loc_disjoint (loc_buffer buf_) (key.footprint h0 k)))
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer buf_) h0 h1) /\
    begin
    let k = (stateful_key a kk).v () h0 k in
    let input_length = if kk > 0 then Spec.size_block a else 0 in
    let input = if kk > 0 then Spec.blake2_key_block a kk k else S.empty in
    S.equal (S.slice (B.as_seq h1 buf_) 0 input_length) input
    end)

let init_key_block a kk k buf_ =
  if kk = 0 then ()
  else
    begin
    (**) let h0 = ST.get () in

    (* Set the end of the buffer to 0 *)
    [@inline_let] let sub_b_len = U32.(block_len a -^ U32.uint_to_t kk) in
    let sub_b = B.sub buf_ (U32.uint_to_t kk) sub_b_len in
    B.fill sub_b (Lib.IntTypes.u8 0) sub_b_len;
    (**) let h1 = ST.get () in
    (**) assert(S.slice (B.as_seq h1 buf_) kk (Spec.size_block a) `S.equal` B.as_seq h1 sub_b);

    (* Copy the key at the beginning of the buffer *)
    Lib.Buffer.update_sub #Lib.Buffer.MUT #uint8 #(U32.uint_to_t (Spec.size_block a))
      buf_ 0ul (U32.uint_to_t kk) (stateful_key_to_buffer k);
    (**) let h2 = ST.get () in
    (**) begin
    (**) let k : LS.lseq uint8 kk = (stateful_key a kk).v () h0 k in
    (**) let buf_v1 : LS.lseq uint8 (Spec.size_block a) = B.as_seq h1 buf_ in
    (**) let buf_v2 : LS.lseq uint8 (Spec.size_block a) = B.as_seq h2 buf_ in

    (* Prove that [buf_] is equal to [key @ create ... 0] *)
    (**) assert(buf_v2 `S.equal` LS.update_sub buf_v1 0 kk k);
    (**) let zeroed : LS.lseq uint8 (Spec.size_block a - kk) = S.create (Spec.size_block a - kk) (Lib.IntTypes.u8 0) in
    (**) assert(B.as_seq h1 sub_b `S.equal` zeroed);
    (**) let key_and_zeroed : LS.lseq uint8 (Spec.size_block a) = Seq.append k zeroed in
    (**) assert(S.equal (S.slice key_and_zeroed 0 kk) k);
    (**) assert(S.equal (S.slice key_and_zeroed kk (Spec.size_block a)) zeroed);
    (**) LS.lemma_update_sub #uint8 #(Spec.size_block a) buf_v1 0 kk k key_and_zeroed;
    (**) assert(buf_v2 `S.equal` key_and_zeroed);

    (* Prove that the initial input is equal to [key @ create ... 0] *)
    (**) let input = Spec.blake2_key_block a kk k in
    (**) let key_block0: LS.lseq uint8 (Spec.size_block a) = S.create (Spec.size_block a) (Lib.IntTypes.u8 0) in
    (**) assert(input `S.equal` LS.update_sub key_block0 0 kk k);
    (**) assert(Seq.equal (LS.sub key_and_zeroed 0 kk) k);
    (**) assert(Seq.equal (LS.sub key_and_zeroed kk (Spec.size_block a - kk))
                          (LS.sub key_block0 kk (Spec.size_block a - kk)));
    (**) LS.lemma_update_sub #uint8 #(Spec.size_block a) key_block0 0 kk k key_and_zeroed;
    (**) assert(input `S.equal` key_and_zeroed)
    (**) end
    end

/// Runtime
/// -------

#push-options "--ifuel 1"// --z3cliopt smt.arith.nl=false"
inline_for_extraction noextract
let blake2 (a : alg)
           (m : valid_m_spec a)
           (kk : key_size a)
           (init : blake2_init_st a m)
           (update_multi : blake2_update_multi_st a m)
           (update_last : blake2_update_last_st a m)
           (finish : blake2_finish_st a m) :
  I.block unit =
  I.Block
    I.Erased (* key management *)

    (stateful_blake2 a m) (* state *)
    (stateful_key a kk)   (* key *)

    unit (* output_length_t *)

    (fun () -> max_input_len a) (* max_input_length *)
    (fun () () -> output_size a) (* output_len *)
    (fun () -> block_len a) (* block_len *)
    (fun () -> block_len a) (* blocks_state_len *)
    (fun () -> if kk > 0 then block_len a else 0ul) (* init_input_len *)

    (fun () k -> if kk > 0 then Spec.blake2_key_block a kk k else S.empty)
    (fun () _k -> init_s a kk) (* init_s *)

    (fun () acc prevlen input -> update_multi_s acc prevlen input) (* update_multi_s *)
    (fun () acc prevlen input -> update_last_s acc prevlen input) (* update_last_s *)
    (fun () _k acc _ -> finish_s #a acc) (* finish_s *)
    (fun () k input l -> spec_s a kk k input) (* spec_s *)

    (* update_multi_zero *)
    (fun () acc prevlen -> update_multi_zero #a acc prevlen)

    (* update_multi_associative *)
    (fun () acc prevlen1 prevlen2 input1 input2 ->
      update_multi_associative acc prevlen1 prevlen2 input1 input2)
    (fun () k input _ ->
     spec_is_incremental a kk k input) (* spec_is_incremental *)
    (fun _ acc -> ()) (* index_of_state *)

    (* init *)
    (fun _ key buf_ acc ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      init_key_block a kk key buf_;
      init h (Lib.IntTypes.size kk) (output_len a))

    (* update_multi *)
    (fun _ acc prevlen blocks len ->
      let wv, hash = acc in
      let nb = len `U32.div` Core.size_block a in
      update_multi #len wv hash (blake2_prevlen a prevlen) blocks nb)

    (* update_last *)
    (fun _ acc prevlen last last_len ->
      let wv, hash = acc in
      update_last #last_len wv hash (blake2_prevlen a prevlen) last_len last)

    (* finish *)
    (fun _ k acc dst _ ->
      [@inline_let] let wv = get_wv acc in
      [@inline_let] let h = get_state_p acc in
      finish (output_len a) dst h)
#pop-options

/// Introducing intermediate definitions for the instantiation

inline_for_extraction noextract
let blake2s_32 kk =
  blake2 Spec.Blake2S Core.M32 kk Blake2s32.blake2s_init Blake2s32.blake2s_update_multi
         Blake2s32.blake2s_update_last Blake2s32.blake2s_finish

inline_for_extraction noextract
let blake2b_32 kk =
  blake2 Spec.Blake2B Core.M32 kk Blake2b32.blake2b_init Blake2b32.blake2b_update_multi
         Blake2b32.blake2b_update_last Blake2b32.blake2b_finish

inline_for_extraction noextract
let empty_key a = I.optional_key () I.Erased (stateful_key a 0)

/// Type abbreviations - makes KaRaMeL use pretty names in the generated code

let blake2s_32_block_state = s Spec.Blake2S Core.M32
let blake2b_32_block_state = s Spec.Blake2B Core.M32
let blake2s_32_state = F.state_s (blake2s_32 0) () (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)
let blake2b_32_state = F.state_s (blake2b_32 0) () (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2B)

/// The incremental hash functions instantiations. Note that we can't write a
/// generic one, because the normalization then performed by KaRaMeL explodes.

/// All those implementations are for non-keyed hash.

inline_for_extraction noextract
let blake2s_32_no_key_alloca =
  F.alloca (blake2s_32 0) () (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  State allocation function when there is no key")]
let blake2s_32_no_key_create_in =
  F.create_in (blake2s_32 0) () (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  (Re-)initialization function when there is no key")]
let blake2s_32_no_key_init =
  F.init (blake2s_32 0) () (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2s_32_no_key_update =
  F.update (blake2s_32 0) (G.hide ()) (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  Finish function when there is no key")]
let blake2s_32_no_key_finish =
  F.mk_finish (blake2s_32 0) () (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  Free state function when there is no key")]
let blake2s_32_no_key_free =
  F.free (blake2s_32 0) (G.hide ()) (s Spec.Blake2S Core.M32) (empty_key Spec.Blake2S)

inline_for_extraction noextract
[@ (Comment "  State allocation function when there is no key")]
let blake2b_32_no_key_alloca =
  F.alloca (blake2b_32 0) () (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2B)

[@ (Comment "  State allocation function when there is no key")]
let blake2b_32_no_key_create_in =
  F.create_in (blake2b_32 0) () (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  (Re)-initialization function when there is no key")]
let blake2b_32_no_key_init =
  F.init (blake2b_32 0) () (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  Update function when there is no key; 0 = success, 1 = max length exceeded")]
let blake2b_32_no_key_update =
  F.update (blake2b_32 0) (G.hide ()) (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  Finish function when there is no key")]
let blake2b_32_no_key_finish =
  F.mk_finish (blake2b_32 0) () (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2S)

[@ (Comment "  Free state function when there is no key")]
let blake2b_32_no_key_free =
  F.free (blake2b_32 0) (G.hide ()) (s Spec.Blake2B Core.M32) (empty_key Spec.Blake2S)
