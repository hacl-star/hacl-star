module Hacl.Streaming.MD

open FStar.HyperStack.ST

/// This file is poorly named. It contains a generic type class instantiation
/// for the streaming functor for any algorithm that fits within the agile hash
/// infrastructure.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.Mul

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

open Spec.Hash.Definitions

/// Maximum input length, but fitting on a 64-bit integer (since the streaming
/// module doesn't bother taking into account lengths that are greater than
/// that). The comment previously was:
///
/// Note that we keep the total length at run-time, on 64 bits, but require that
/// it abides by the size requirements for the smaller hashes -- we're not
/// interested at this stage in having an agile type for lengths that would be
/// up to 2^125 for SHA384/512.

inline_for_extraction noextract
let max_input_len64 a: U64.(x:t { 0 < v x /\ v x `less_than_max_input_length` a }) =
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 ->
      assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64);
      normalize_term_spec (pow2 61 - 1);
      U64.uint_to_t (normalize_term (pow2 61 - 1))
  | SHA2_384 | SHA2_512 ->
      assert_norm (pow2 64 < pow2 125 - 1);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2S ->
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2B ->
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | SHA3_256 ->
      // TODO: relax this?
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))

open Hacl.Streaming.Interface

open Hacl.Hash.Definitions
module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

// It would be better to define this as md_alg, but Hacl.Streaming.SHA3 uses hacl_md,
// while SHA3 is not an MD algorithm
inline_for_extraction noextract
let alg = a:hash_alg{not (is_blake a)}

let _: squash (inversion hash_alg) = allow_inversion hash_alg

inline_for_extraction noextract
let word (a: alg) = if is_sha2 a then Hacl.Spec.SHA2.Vec.(element_t a M32) else word a

// Big up for Aymeric who dug this one to help me make the coercion work.
unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

inline_for_extraction noextract
let init_elem (a : alg) : word a =
  if is_sha2 a then
    Hacl.Spec.SHA2.Vec.(zero_element a M32)
  else match a with
  | MD5 | SHA1 -> Lib.IntTypes.u32 0
  | SHA3_256 -> Lib.IntTypes.u64 0

inline_for_extraction noextract
let sha2_mb_state = Lib.Buffer.lbuffer (Lib.IntVector.vec_t Lib.IntTypes.U32 1) 8ul

let _ = assert_norm (
  let open Hacl.Impl.SHA2.Core in
  let open Hacl.Spec.SHA2.Vec in
  state_t SHA2_256 M32 == sha2_mb_state)

let multiseq_is_seq a l: Lemma
  (requires is_sha2 a)
  (ensures (
    let open Hacl.Impl.SHA2.Core in
    let open Hacl.Spec.SHA2.Vec in
    multiseq (lanes a M32) l == s:S.seq uint8 { S.length s = l }))
=
  let open Hacl.Impl.SHA2.Core in
  let open Hacl.Spec.SHA2.Vec in
  let open Lib.NTuple in
  let open Lib.Sequence in
  assert (lanes a M32 == 1);
  calc (==) {
    m:S.seq uint8 { S.length m = l };
  (==) { }
    m:S.seq uint8 { (S.length m <: nat) == (l <: nat) };
  (==) { _ by (FStar.Tactics.trefl ()) }
    S.lseq uint8 l;
  }

let multiseq_hash_is_hash a: Lemma
  (requires is_sha2 a)
  (ensures (
    let open Hacl.Impl.SHA2.Core in
    let open Hacl.Spec.SHA2.Vec in
    multiseq (lanes a M32) (hash_length a) == Spec.Agile.Hash.bytes_hash a))
=
  let open Hacl.Impl.SHA2.Core in
  let open Hacl.Spec.SHA2.Vec in
  let open Lib.NTuple in
  let open Lib.Sequence in
  assert (lanes a M32 == 1);
  calc (==) {
    Spec.Hash.Definitions.bytes_hash a;
  (==) { _ by (FStar.Tactics.trefl ()) }
    m:S.seq uint8 { S.length m = Spec.Agile.Hash.hash_length a };
  (==) { multiseq_is_seq a (Spec.Agile.Hash.hash_length a) }
    S.lseq uint8 (hash_length a);
  }

let multibuf_is_buf (len: Lib.IntTypes.size_t): Lemma
  (ensures Lib.MultiBuffer.multibuf 1 len == x:B.buffer uint8 { B.length x == Lib.IntTypes.v len })
=
  let open Lib.Buffer in
  calc (==) {
    Lib.MultiBuffer.multibuf 1 len;
  (==) { }
    Lib.Buffer.lbuffer uint8 len;
  (==) { _ by FStar.Tactics.(norm [ iota; zeta; delta_only [ `%lbuffer; `%lbuffer_t; `%buffer_t ]]; trefl ()) }
    x:B.buffer uint8 { B.length x == Lib.IntTypes.v len };
  }

inline_for_extraction noextract
let lib_of_agile (#a: alg { is_sha2 a }) (x: Spec.Agile.Hash.bytes_hash a):
  y:Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) (Spec.Agile.Hash.hash_length a)) { x === y }
=
  multiseq_hash_is_hash a;
  coerce #Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) (Spec.Agile.Hash.hash_length a)) x

inline_for_extraction noextract
let agile_of_lib (#a: alg { is_sha2 a }) (y:Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) (Spec.Agile.Hash.hash_length a))):
  x: Spec.Agile.Hash.bytes_hash a { x === y }
=
  multiseq_hash_is_hash a;
  coerce #(Spec.Agile.Hash.bytes_hash a) y

inline_for_extraction noextract
let lib_of_buffer #len (x: B.buffer uint8):
  Pure (Lib.MultiBuffer.multibuf 1 len) (requires B.length x == Lib.IntTypes.v len) (ensures fun _ -> True)
=
  multibuf_is_buf len;
  coerce #(Lib.MultiBuffer.multibuf 1 len) #(x:B.buffer uint8 { B.length x == Lib.IntTypes.v len }) x

inline_for_extraction noextract
let buffer_of_lib #len (x: Lib.MultiBuffer.multibuf 1 len):
  Pure (B.buffer uint8) (requires True) (ensures fun x -> B.length x == Lib.IntTypes.v len)
=
  multibuf_is_buf len;
  coerce #(x:B.buffer uint8 { B.length x == Lib.IntTypes.v len }) #(Lib.MultiBuffer.multibuf 1 len) x

inline_for_extraction noextract
let state_t (a : alg) = stateful_buffer (word a) (D.impl_state_len (|a, ()|)) (init_elem a)

let eq_word_element (a:alg { is_sha2 a }) : Lemma (word a == Hacl.Spec.SHA2.Vec.(element_t a M32))
  = ()

let eq_length_lib_state (a:alg { is_sha2 a }) (b:B.buffer Hacl.Spec.SHA2.Vec.(element_t a M32))
  : Lemma ( (B.len b == D.impl_state_len (| a, () |)) == (B.length b == Lib.IntTypes.v 8ul))
  = FStar.PropositionalExtensionality.apply
      (B.len b == D.impl_state_len (| a, () |))
      (B.length b == Lib.IntTypes.v 8ul)

let lib_of_state (a: alg { is_sha2 a }) (s: (state_t a).s ()): Lemma
  (ensures (state_t a).s () == Lib.Buffer.lbuffer Hacl.Spec.SHA2.Vec.(element_t a M32) 8ul)
=
  let open Lib.Buffer in
  assert (D.impl_state_len (| a, () |) == 8ul);
  calc (==) {
    (state_t a).s ();
  (==) { _ by FStar.Tactics.(trefl ()) }
    b:B.buffer (word a) { B.len b == D.impl_state_len (| a, () |) };
  // Somehow, having eq_word_element as a local definition leads to a tactic failure,
  // where the lemma application cannot be typechecked in the current context because
  // eq_word_element is not found in the context
  (==) { _ by FStar.Tactics.(l_to_r [`eq_word_element]) }
  // Same issue for eq_length_lib_state
    b:B.buffer Hacl.Spec.SHA2.Vec.(element_t a M32) { B.len b == D.impl_state_len (| a, () |) };
  (==) { _ by FStar.Tactics.(l_to_r [`eq_length_lib_state]) }
    b:B.buffer Hacl.Spec.SHA2.Vec.(element_t a M32) { B.length b == Lib.IntTypes.v 8ul };
  (==) { _ by FStar.Tactics.(norm [ zeta; iota; delta_only [ `%lbuffer; `%lbuffer_t; `%buffer_t ] ]; trefl ()) }
    Lib.Buffer.lbuffer Hacl.Spec.SHA2.Vec.(element_t a M32) 8ul;
  }

inline_for_extraction noextract
let update_multi_s (a : alg) () acc (prevlen : nat) input =
  Agile.(update_multi a acc () input)

noextract
let update_multi_zero (a : alg) () acc (prevlen : nat) :
  Lemma(update_multi_s a () acc prevlen S.empty == acc) = Spec.Hash.Lemmas.update_multi_zero a acc

noextract
let multiseq_empty (a: alg { is_sha2 a }): Hacl.Spec.SHA2.Vec.(multiseq (lanes a M32) 0) =
  let open Hacl.Spec.SHA2.Vec in
  multiseq_is_seq a 0;
  coerce #(multiseq (lanes a M32) 0) #(s:S.seq uint8 { S.length s == 0 }) (S.empty #uint8)

#push-options "--ifuel 1"

// TODO: this is the third copy of this lemma!! why?!
noextract
let update_multi_associative (a : alg) () acc (prevlen1 prevlen2 : nat)
                             (input1 input2 : S.seq uint8) :
    Lemma
    (requires (
      S.length input1 % U32.v (D.block_len a) = 0 /\
      S.length input2 % U32.v (D.block_len a) = 0))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v (D.block_len a) = 0 /\
      update_multi_s a () (update_multi_s a () acc prevlen1 input1) prevlen2 input2 ==
        update_multi_s a () acc prevlen1 input)) =
  Spec.Hash.Lemmas.update_multi_associative a acc input1 input2
#pop-options

val update_nblocks_vec_m32_is_repeat_blocks_multi:
     a:sha2_alg
  -> len:Hacl.Spec.SHA2.len_lt_max_a_t a{len % block_length a = 0}
  -> b:Seq.lseq uint8 len
  -> st0:Hacl.Spec.SHA2.Vec.(state_spec a M32) ->
  Lemma
   (let open Lib.Sequence in
    let open Hacl.Spec.SHA2.Vec in
    let b = b <: multiseq 1 len in
    let st = update_nblocks #a #M32 len b st0 in

    let st0_m32 = (state_spec_v st0).[0] <: words_state a in
    let st_m32 = (state_spec_v st).[0] <: words_state' a in
    st_m32 == repeat_blocks_multi (block_length a) b (Hacl.Spec.SHA2.update a) st0_m32)

let update_nblocks_vec_m32_is_repeat_blocks_multi a len b st0 =
  let open Lib.NTuple in
  let open Lib.Sequence in
  let open Hacl.Spec.SHA2.Vec in
  let b = b <: multiseq 1 len in
  let st1 = update_nblocks #a #M32 len b st0 in

  let st0_m32_t = (state_spec_v st0).[0] <: words_state a in
  let st1_m32_t = (state_spec_v st1).[0] <: words_state a in
  let st1_spec_m32 = Hacl.Spec.SHA2.update_nblocks a len b st0_m32_t in

  Hacl.Spec.SHA2.EquivScalar.update_nblocks_is_repeat_blocks_multi a len b st0_m32_t;
  assert (st1_spec_m32 ==
    repeat_blocks_multi (block_length a) b (Hacl.Spec.SHA2.update a) st0_m32_t);

  Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #a #M32 len b st0 0;
  tup1_lemma b;
  assert (b.(|0|) == b);
  assert (st1_m32_t == st1_spec_m32)

let state_spec_v_extensionality = Hacl.SHA2.Scalar32.state_spec_v_extensionality

let repeati_associative (a : alg { is_sha2 a })
  (acc: Hacl.Spec.SHA2.Vec.(state_spec a M32))
  (input1 input2 : S.seq uint8) :
    Lemma
    (requires (
      S.length input1 + S.length input2 <= Some?.v (Spec.Agile.Hash.max_input_length a) /\
      S.length input1 % U32.v (D.block_len a) = 0 /\
      S.length input2 % U32.v (D.block_len a) = 0))
    (ensures (
      let open Hacl.Spec.SHA2.Vec in
      let input = S.append input1 input2 in
      S.length input % U32.v (D.block_len a) = 0 /\
      update_nblocks #a #M32 (S.length input) (input <: multiseq 1 (S.length input)) acc ==
      update_nblocks #a #M32 (S.length input2) (input2 <: multiseq 1 (S.length input2))
        (update_nblocks #a #M32 (S.length input1) (input1 <: multiseq 1 (S.length input1)) acc)))
=
  let open Lib.NTuple in
  let open Lib.Sequence in
  let open Hacl.Spec.SHA2.Vec in
  let input = S.append input1 input2 in
  let len = S.length input in
  let len1 = S.length input1 in
  let len2 = S.length input2 in
  let input = input <: multiseq 1 len in
  let input1 = input1 <: multiseq 1 len1 in
  let input2 = input2 <: multiseq 1 len2 in

  let acc_m32 = (state_spec_v acc).[0] <: words_state a in
  let bl = block_length a in
  Lib.Sequence.Lemmas.repeat_blocks_multi_split bl
    len1 input (Hacl.Spec.SHA2.update a) acc_m32;

  Seq.lemma_eq_intro (Seq.slice input 0 len1) input1;
  Seq.lemma_eq_intro (Seq.slice input len1 len) input2;
  assert (Seq.slice input 0 len1 == input1);
  assert (Seq.slice input len1 len == input2);
  assert (repeat_blocks_multi bl input (Hacl.Spec.SHA2.update a) acc_m32 ==
    repeat_blocks_multi bl input2 (Hacl.Spec.SHA2.update a)
      (repeat_blocks_multi bl input1 (Hacl.Spec.SHA2.update a) acc_m32));

  let acc1 = update_nblocks #a #M32 len1 input1 acc in
  let acc2 = update_nblocks #a #M32 len2 input2 acc1 in
  let acc3 = update_nblocks #a #M32 len input acc in
  // let acc1_m32 = (state_spec_v acc1).[0] <: words_state' a in
  // let acc1_m32_t = (acc1_m32, ()) <: words_state a in
  // let acc2_m32 = (state_spec_v acc2).[0] <: words_state' a in
  // let acc2_m32_t = (acc2_m32, ()) <: words_state a in
  // let acc3_m32 = (state_spec_v acc3).[0] <: words_state' a in
  // let acc3_m32_t = (acc3_m32, ()) <: words_state a in

  update_nblocks_vec_m32_is_repeat_blocks_multi a len input acc;
  update_nblocks_vec_m32_is_repeat_blocks_multi a len1 input1 acc;
  update_nblocks_vec_m32_is_repeat_blocks_multi a len2 input2 acc1;
  // assert (acc1_m32_t == repeat_blocks_multi bl input1 (Hacl.Spec.SHA2.update a) acc_m32);
  // assert (acc2_m32_t == repeat_blocks_multi bl input2 (Hacl.Spec.SHA2.update a) acc1_m32_t);
  // assert (acc3_m32_t == repeat_blocks_multi bl input (Hacl.Spec.SHA2.update a) acc_m32);
  // assert (acc3_m32_t == acc2_m32_t);
  state_spec_v_extensionality a acc2 acc3

val hash_vec_m32_is_repeat_blocks:
     a:sha2_alg
  -> len:Hacl.Spec.SHA2.len_lt_max_a_t a
  -> b:Seq.lseq uint8 len
  -> st0:Hacl.Spec.SHA2.Vec.(state_spec a M32) ->
  Lemma
   (let open Lib.Sequence in
    let open Hacl.Spec.SHA2.Vec in
    let totlen : len_t a = Hacl.Spec.SHA2.mk_len_t a len in
    let b = b <: multiseq 1 len in
    let st = update_nblocks #a #M32 len b st0 in
    let rem = len % block_length a in
    let mb = Seq.slice b (len - rem) len in
    let mb = mb <: multiseq 1 rem in
    let st_last = update_last #a #M32 totlen rem mb st in

    let st0_m32 = (state_spec_v st0).[0] <: words_state a in
    let st_last_m32 = (state_spec_v st_last).[0] <: words_state a in

    st_last_m32 == repeat_blocks (block_length a) b
      (Hacl.Spec.SHA2.update a) (Hacl.Spec.SHA2.update_last a totlen) st0_m32)

let hash_vec_m32_is_repeat_blocks a len b st0 =
  let open Lib.NTuple in
  let open Lib.Sequence in
  let open Hacl.Spec.SHA2.Vec in
  let totlen : len_t a = Hacl.Spec.SHA2.mk_len_t a len in
  let rem = len % block_length a in
  let mb = Seq.slice b (len - rem) len in
  let b = b <: multiseq 1 len in
  let mb = mb <: multiseq 1 rem in
  let st1 = update_nblocks #a #M32 len b st0 in
  let st2 = update_last #a #M32 totlen rem mb st1 in

  let st0_m32_t = (state_spec_v st0).[0] <: words_state a in
  let st1_m32_t = (state_spec_v st1).[0] <: words_state a in
  let st2_m32_t = (state_spec_v st2).[0] <: words_state a in

  let st1_spec_m32 = Hacl.Spec.SHA2.update_nblocks a len b st0_m32_t in
  let st2_spec_m32 = Hacl.Spec.SHA2.update_last a totlen rem mb st1_spec_m32 in
  Hacl.Spec.SHA2.EquivScalar.hash_is_repeat_blocks a len b st0_m32_t;
  assert (st2_spec_m32 ==
    Lib.Sequence.repeat_blocks (block_length a) b
      (Hacl.Spec.SHA2.update a) (Hacl.Spec.SHA2.update_last a totlen) st0_m32_t);

  Hacl.Spec.SHA2.Equiv.update_nblocks_lemma_l #a #M32 len b st0 0;
  // assert ((state_spec_v (update_nblocks len b st0)).[0] ==
  //   Pervasives.fst (Hacl.Spec.SHA2.update_nblocks a len b.(|0|) ((state_spec_v st0).[0], ())));
  // assert ((state_spec_v st1).[0] ==
  //   Pervasives.fst (Hacl.Spec.SHA2.update_nblocks a len b.(|0|) st0_m32_t));
  tup1_lemma b;
  assert (b.(|0|) == b);
  assert (st1_m32_t == st1_spec_m32);

  Hacl.Spec.SHA2.Equiv.update_last_lemma_l totlen rem mb st1 0;
  tup1_lemma mb;
  assert (mb.(|0|) == mb);
  assert (st2_m32_t == st2_spec_m32)

val update_nblocks_with_last_sliced:
     a:alg { is_sha2 a }
  -> len:Hacl.Spec.SHA2.len_lt_max_a_t a
  -> b:Seq.lseq uint8 len
  -> st0:Hacl.Spec.SHA2.Vec.(state_spec a M32) ->
  Lemma
   (let open Hacl.Spec.SHA2.Vec in
    let b = b <: multiseq 1 len in
    let st = update_nblocks #a #M32 len b st0 in

    let rem = len % block_length a in
    let blocks = Seq.slice b 0 (len - rem) in
    let blocks = blocks <: multiseq 1 (len - rem) in
    let st_sliced = update_nblocks #a #M32 (len - rem) blocks st0 in

    let totlen : len_t a = Hacl.Spec.SHA2.mk_len_t a len in
    let mb = Seq.slice b (len - rem) len in
    let mb = mb <: multiseq 1 rem in

    update_last #a #M32 totlen rem mb st ==
    update_last #a #M32 totlen rem mb st_sliced)

let update_nblocks_with_last_sliced a len b st0 =
  let open Lib.NTuple in
  let open Lib.Sequence in
  let open Hacl.Spec.SHA2.Vec in
  let totlen : len_t a = Hacl.Spec.SHA2.mk_len_t a len in
  let b = b <: multiseq 1 len in
  let st = update_nblocks #a #M32 len b st0 in
  let rem = len % block_length a in
  let mb = Seq.slice b (len - rem) len in
  let mb = mb <: multiseq 1 rem in
  let st_last = update_last #a #M32 totlen rem mb st in

  let st0_m32_t = (state_spec_v st0).[0] <: words_state a in
  //let st_m32 = (state_spec_v st).[0] <: words_state' a in
  //let st_m32_t = (st_m32, ()) <: words_state a in
  let st_last_m32_t = (state_spec_v st_last).[0] <: words_state a in

  hash_vec_m32_is_repeat_blocks a len b st0;
  assert (st_last_m32_t == repeat_blocks (block_length a) b
    (Hacl.Spec.SHA2.update a) (Hacl.Spec.SHA2.update_last a totlen) st0_m32_t);
  Lib.Sequence.Lemmas.lemma_repeat_blocks_via_multi (block_length a) b
    (Hacl.Spec.SHA2.update a) (Hacl.Spec.SHA2.update_last a totlen) st0_m32_t;

  let blocks = Seq.slice b 0 (len - rem) in
  let blocks = blocks <: multiseq 1 (len - rem) in
  assert (st_last_m32_t ==
    Hacl.Spec.SHA2.update_last a totlen rem mb
      (repeat_blocks_multi (block_length a) blocks
        (Hacl.Spec.SHA2.update a) st0_m32_t));

  let st_sliced = update_nblocks #a #M32 (len - rem) blocks st0 in
  let st_sliced_last = update_last #a #M32 totlen rem mb st_sliced in

  let st_sliced_m32_t = (state_spec_v st_sliced).[0] <: words_state a in
  let st_slicedl_m32_t = (state_spec_v st_sliced_last).[0] <: words_state a in

  update_nblocks_vec_m32_is_repeat_blocks_multi a (len - rem) blocks st0;
  assert (st_sliced_m32_t ==
    repeat_blocks_multi (block_length a) blocks
      (Hacl.Spec.SHA2.update a) st0_m32_t);

  Hacl.Spec.SHA2.Equiv.update_last_lemma_l totlen rem mb st_sliced 0;
  tup1_lemma mb;
  assert (mb.(|0|) == mb);
  assert (st_slicedl_m32_t == st_last_m32_t);
  state_spec_v_extensionality a st_last st_sliced_last

let lemma_split_at_last_lazy (l:pos) (b: S.seq uint8) :
  Lemma
     (requires S.length b % l <> 0 \/ S.length b == 0)
     (ensures (let blocks, last = Lib.UpdateMulti.split_at_last_lazy l b in
        let len = Seq.length b in
        let rem = len % l in
        let blocks_s = Seq.slice b 0 (len - rem) in
        let last_s = Seq.slice b (len - rem) len in
        blocks == blocks_s /\ last == last_s)) =

  let blocks, last = Lib.UpdateMulti.split_at_last_lazy l b in
  let len = Seq.length b in
  let rem_s = len % l in
  let blocks_s = Seq.slice b 0 (len - rem_s) in
  let last_s = Seq.slice b (len - rem_s) len in

  let n, rem = Lib.UpdateMulti.split_at_last_lazy_nb_rem l len in
  assert (rem % l == len % l)

val update_last_one_block (a: alg { is_sha2 a })
  (totlen:len_t a)
  (b : Hacl.Spec.SHA2.Vec.multiseq Hacl.Spec.SHA2.Vec.(lanes a M32) (block_length a))
  (s : Hacl.Spec.SHA2.Vec.multiseq Hacl.Spec.SHA2.Vec.(lanes a M32) 0)
  (st : Hacl.Spec.SHA2.Vec.state_spec a Hacl.Spec.SHA2.Vec.M32)
  : Lemma
      // Why is that not automatically derived
      (requires block_length a `less_than_max_input_length` a)
      (ensures Hacl.Spec.SHA2.Vec.(
         update_last totlen (block_length a) b st ==
          update_last totlen 0 s (update_block #a #M32 (block_length a) b 0 st)))

let sub_update_sub (#a:Type) (len:Lib.IntTypes.size_nat)
  (sub_st:Lib.IntTypes.size_nat{sub_st <= len})
  (sub_len:Lib.IntTypes.size_nat{sub_st + sub_len <= len})
  (i:Lib.Sequence.lseq a len)
  (start:Lib.IntTypes.size_nat)
  (n:Lib.IntTypes.size_nat{start + n <= sub_len})
  (x:Lib.Sequence.lseq a n)
  : Lemma (Lib.Sequence.(update_sub (sub i sub_st sub_len) start n x ==
      sub (update_sub i (sub_st + start) n x) sub_st sub_len))
  = let open Lib.Sequence in
    let s1:lseq a sub_len = update_sub (sub i sub_st sub_len) start n x in
    let s2:lseq a sub_len = sub (update_sub i (sub_st + start) n x) sub_st sub_len in
    let aux (k:nat{k < sub_len}) : Lemma (index s1 k == index s2 k) =
      if k < start || k >= start + n then ()
      else
      calc (==) {
        index s2 k;
        (eq2 #a) { } // Unrolling sub. Need to expand == to help with typing
        index (update_sub i (sub_st + start) n x) (sub_st + k);
        (==) { }
        index (sub (update_sub i (sub_st + start) n x) (sub_st + start) n) (k - start);
        (==) { } // By postcondition of update_sub
        index x (k - start);
        (==) { () }
        index s1 k;
      }
    in Classical.forall_intro aux;
    assert (s1 `equal` s2)

let update_last_one_block a totlen b s st =
  let open Lib.NTuple in
  let open Lib.IntTypes in
  let open Lib.Sequence in
  let open Hacl.Spec.SHA2.Vec in
  let len1 = 0 in
  let len2 = block_length a in

  let blocks1 = padded_blocks a len1 in
  assert (blocks1 == 1);
  let blocks2 = padded_blocks a len2 in
  assert (blocks2 == 2);

  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in
  let totlen_seq = Lib.ByteSequence.uint_to_bytes_be #(len_int_type a) total_len_bits in

  let (b01, b11) = load_last #a #M32 totlen_seq (1 * block_length a) len1 s in
  let (b02, b12) = load_last #a #M32 totlen_seq (2 * block_length a) len2 b in

  assert (update_last totlen len2 b st == update b12 (update b02 st));

  let l01, _ = load_last_blocks #a totlen_seq (block_length a) 0 s.(|0|) in
  let l02, l12 = load_last_blocks #a totlen_seq (2 * block_length a) len2 b.(|0|) in

  let last = create (2 * block_length a) (u8 0) in
  let last1 = update_sub last 0 len2 b.(|0|) in
  let last2 = last1.[len2] <- u8 0x80 in
  let start = 2 * block_length a - len_length a in
  let last3 = update_sub last2 start (len_length a) totlen_seq in

  assert (l02 `Lib.Sequence.equal` b.(|0|));

  let open FStar.Tactics in
  assert (load_last #a #M32 totlen_seq (2 * block_length a) len2 b ==
    load_last1 #a totlen_seq (2 * block_length a) len2 b) by (norm [delta_only [`%load_last]]);

  tup1_lemma b02;
  tup1_lemma b;
  assert (b02 == b);

  let last1' = update_sub last 0 len1 s.(|0|) in
  assert (last `Lib.Sequence.equal` last1');

  let last2' = last.[len1] <- u8 0x80 in
  let last3' = update_sub last2' (block_length a - len_length a) (len_length a) totlen_seq in
  assert (l01 == sub last3' 0 (block_length a));
  assert (l12 == sub last3 (block_length a) (block_length a));

  // To trigger the right patterns, we need to alternate between
  // Seq.equal and Lib.Sequence.equal...
  let lastone = create len2 (u8 0) in
  assert (lastone `S.equal` S.create len2 (u8 0));
  assert (sub last1 len2 len2 `Lib.Sequence.equal` S.create len2 (u8 0));
  let last2one = lastone.[0] <- u8 0x80 in
  assert (last2one `Lib.Sequence.equal` (sub last2 len2 len2));
  assert (last2one `S.equal` (sub last2' 0 len2));

  let last3one = update_sub last2one (len2 - len_length a) (len_length a) totlen_seq in

  assert (last3one == update_sub (sub last2 len2 len2) (len2 - len_length a) (len_length a) totlen_seq);

  sub_update_sub (2 * block_length a) len2 len2 last2 (len2 - len_length a) (len_length a) totlen_seq;

  assert (last3one == sub last3 len2 len2);

  sub_update_sub (2 * block_length a) 0 len2 last2' (len2 - len_length a) (len_length a) totlen_seq;
  assert (last3one == sub last3' 0 len2);
  assert (l01 == l12);

  assert (load_last #a #M32 totlen_seq (block_length a) 0 s ==
    load_last1 #a totlen_seq (block_length a) 0 s) by (norm [delta_only [`%load_last]]);

  tup1_lemma b12;
  tup1_lemma b01;

  assert (b12 == b01);

  Lib.NTuple.eq_intro (get_multiblock_spec #a #M32 len2 b 0) b;
  assert (get_multiblock_spec len2 b 0 == b);
  assert (update_block #a #M32 len2 b 0 st == update b st);

  assert (update_last totlen 0 s (update b st) == update b01 (update b st))


let sha2_mb_is_incremental (a: alg { is_sha2 a }) (input: S.seq uint8):
    Lemma (requires S.length input <= Some?.v (Spec.Agile.Hash.max_input_length a))
    (ensures (
      let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
      (**) Math.Lemmas.modulo_lemma 0 (U32.v (block_len a));
      let open Hacl.Spec.SHA2.Vec in
      let hash0 = init a M32 in
      let hash1 = update_nblocks #a #M32 (S.length blocks) (blocks <: multiseq 1 (S.length blocks)) hash0 in
      let totlen: len_t a = Hacl.Spec.SHA2.mk_len_t a (S.length input) in
      let hash2 = update_last #a #M32 totlen (S.length last) (last <: multiseq 1 (S.length last)) hash1 in
      let hash3 = finish hash2 in
      agile_of_lib hash3 `S.equal` Spec.Agile.Hash.hash a input))
=
  let open Lib.NTuple in
  let open Lib.Sequence in
  let open Hacl.Spec.SHA2.Vec in
  let blocks, last = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len a)) input in
  (**) Math.Lemmas.modulo_lemma 0 (U32.v (block_len a));

  let hash0 = init a M32 in

  let len = S.length input in
  let totlen: len_t a = Hacl.Spec.SHA2.mk_len_t a len in
  let input = input <: multiseq 1 len in

  let rem = len % block_length a in
  let input_blocks = Seq.slice input 0 (len - rem) in
  let input_blocks = input_blocks <: multiseq 1 (len - rem) in
  let mb = Seq.slice input (len - rem) len in
  let mb = mb <: multiseq 1 rem in


  let blocks = blocks <: multiseq 1 (S.length blocks) in
  let last = last <: multiseq 1 (S.length last) in

  let st = update_nblocks #a #M32 len input hash0 in
  let st_last = update_last #a #M32 totlen rem mb st in
  let st_finish = finish st_last in


  if rem = 0 && len <> 0 then (
    assert (mb == S.empty);
    assert (input_blocks `Seq.equal` (blocks `S.append` last));

    let hash1 = update_nblocks #a #M32 (len - block_length a) blocks hash0 in
    let hash2 = update_last #a #M32 totlen (block_length a) last hash1 in
    let hash3 = finish hash2 in

    repeati_associative a hash0 blocks last;
    assert (st == update_nblocks #a #M32 (block_length a) last hash1);
    Lib.LoopCombinators.unfold_repeati 1 (update_block #a #M32 (block_length a) last) hash1 0;
    Lib.LoopCombinators.eq_repeati0 1 (update_block #a #M32 (block_length a) last) hash1;
    assert (st == update_block #a #M32 (block_length a) last 0 hash1);

    update_last_one_block a totlen last mb hash1;
    assert (hash2 == st_last);

    assert ((get_multilast_spec #a #M32 len input).(|0|) ==
      Seq.slice input.(|0|) (len - rem) len);
    tup1_lemma input;
    assert (input.(|0|) == input);
    tup1_lemma mb;
    assert (mb.(|0|) == mb);
    assert ((get_multilast_spec #a #M32 len input).(|0|) == mb.(|0|));
    Lib.NTuple.eq_intro (get_multilast_spec #a #M32 len input) mb;
    assert (get_multilast_spec #a #M32 len input == mb);
    assert (hash3 == hash len input);
    Hacl.Spec.SHA2.Equiv.hash_agile_lemma #a #M32 len input;
    assert ((hash #a #M32 len input).(|0|) == Spec.Agile.Hash.hash a input.(|0|));
    assert (hash3.(|0|) == Spec.Agile.Hash.hash a input.(|0|));
    assert (hash3.(|0|) == Spec.Agile.Hash.hash a input);
    //let hash3 = hash3.(|0|) <: lseq uint8 (hash_length a) in
    //assert (hash3 == Spec.Agile.Hash.hash a input);
    //let hash3_s = hash3 <: multiseq 1 (hash_length a) in
    //assert (agile_of_lib #a hash3_s == hash3);
    ntup1_lemma #_ #1 hash3;
    assert (agile_of_lib #a hash3 == hash3.(|0|));
    assert (agile_of_lib #a hash3 == Spec.Agile.Hash.hash a input)

  ) else (
    lemma_split_at_last_lazy (block_length a) input;
    assert (mb == last /\ input_blocks == blocks);

    let hash1 = update_nblocks #a #M32 (len - rem) blocks hash0 in
    let hash2 = update_last #a #M32 totlen rem last hash1 in
    let hash3 = finish hash2 in

    update_nblocks_with_last_sliced a len input hash0;
    assert (hash2 == st_last);
    assert (hash3 == st_finish);

    assert ((get_multilast_spec #a #M32 len input).(|0|) ==
      Seq.slice input.(|0|) (len - rem) len);
    tup1_lemma input;
    assert (input.(|0|) == input);
    tup1_lemma mb;
    assert (mb.(|0|) == mb);
    assert ((get_multilast_spec #a #M32 len input).(|0|) == mb.(|0|));
    Lib.NTuple.eq_intro (get_multilast_spec #a #M32 len input) mb;
    assert (get_multilast_spec #a #M32 len input == mb);
    assert (hash3 == hash len input);
    Hacl.Spec.SHA2.Equiv.hash_agile_lemma #a #M32 len input;
    assert ((hash #a #M32 len input).(|0|) == Spec.Agile.Hash.hash a input.(|0|));
    assert (hash3.(|0|) == Spec.Agile.Hash.hash a input.(|0|));
    assert (hash3.(|0|) == Spec.Agile.Hash.hash a input);
    //let hash3 = hash3.(|0|) <: lseq uint8 (hash_length a) in
    //assert (hash3 == Spec.Agile.Hash.hash a input);
    //let hash3_s = hash3 <: multiseq 1 (hash_length a) in
    //assert (agile_of_lib #a hash3_s == hash3);
    ntup1_lemma #_ #1 hash3;
    assert (agile_of_lib #a hash3 == hash3.(|0|));
    assert (agile_of_lib #a hash3 == Spec.Agile.Hash.hash a input)
  )

// Extraction loops otherwise. Using every flavor of noextract known to man.
noextract [@@ noextract_to "krml" ]
let live_multi_of_live #len (h:HS.mem) (b:Lib.MultiBuffer.multibuf 1 len): Lemma
  (requires (
    B.live h (buffer_of_lib #len b)))
  (ensures Lib.MultiBuffer.live_multi h b)
=
  let open Lib.Buffer in
  let open Lib.NTuple in
  let foo (i: nat): Lemma (requires (i < 1)) (ensures live h b.(|i|)) [ SMTPat (live h b.(|i|)) ]=
    assert (Lib.MultiBuffer.multibuf 1 len == Lib.Buffer.lbuffer uint8 len);
    assert (live h (b <: Lib.Buffer.lbuffer uint8 len));
    Lib.NTuple.ntup1_lemma #(Lib.Buffer.lbuffer uint8 len) #1 b;
    assert (b.(|i|) == b)
  in
  ()

noextract [@@ noextract_to "krml" ]
let disjoint_multi_of_disjoint #a #len #len' (b:Lib.MultiBuffer.multibuf 1 len)
  (b': Lib.Buffer.lbuffer a len'): Lemma
  (requires (
    B.disjoint (buffer_of_lib #len b) (b' <: B.buffer a)))
  (ensures Lib.MultiBuffer.disjoint_multi b b')
=
  let open Lib.Buffer in
  let open Lib.NTuple in
  let foo (i: nat): Lemma (requires (i < 1)) (ensures disjoint b.(|i|) b') [ SMTPat (disjoint b.(|i|) b') ]=
    assert (Lib.MultiBuffer.multibuf 1 len == Lib.Buffer.lbuffer uint8 len);
    assert (disjoint (b <: Lib.Buffer.lbuffer uint8 len) b');
    Lib.NTuple.ntup1_lemma #(Lib.Buffer.lbuffer uint8 len) #1 b;
    assert (b.(|i|) == b)
  in
  ()


/// This proof usually succeeds fast but we increase the rlimit for safety
#push-options "--z3rlimit 500 --ifuel 1"
inline_for_extraction noextract
let hacl_md (a:alg)// : block unit =
  =
  assert_norm (word SHA3_256 == Lib.IntTypes.uint64);
  Block
    Erased
    (state_t a)
    (stateful_unused unit)

    (fun () -> max_input_len64 a)
    (fun () -> Hacl.Hash.Definitions.hash_len a)
    (fun () -> Hacl.Hash.Definitions.block_len a)
    (fun () -> Hacl.Hash.Definitions.block_len a)

    (fun () _ ->
      if is_sha2 a then
        Hacl.Spec.SHA2.Vec.(init a M32)
      else
        Spec.Agile.Hash.init a)
    (fun () acc prevlen blocks ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2.Vec in
        update_nblocks #a #M32 (S.length blocks) (blocks <: multiseq 1 (S.length blocks)) acc
      else
        update_multi_s a () acc prevlen blocks)
    (fun () acc prevlen input ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2 in
        let totlen: len_t a = mk_len_t a (prevlen + S.length input) in
        Hacl.Spec.SHA2.Vec.(update_last #a #M32 totlen (S.length input) (input <: multiseq 1 (S.length input)) acc)
      else if is_sha3 a then
        Spec.Hash.Incremental.(update_last a acc () input)
      else
        Spec.Hash.Incremental.(update_last a acc prevlen input))
    (fun () _ acc ->
      if is_sha2 a then
        let _ = multiseq_hash_is_hash a in
        agile_of_lib Hacl.Spec.SHA2.Vec.(finish #a #M32 acc)
      else
        Spec.Hash.PadFinish.(finish a acc))
    (fun () _ s -> Spec.Agile.Hash.(hash a s))

    (fun i h prevlen ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2.Vec in
        Lib.LoopCombinators.eq_repeati0 (0 / block_length a) (update_block #a #M32 0 (multiseq_empty a)) h
      else
        update_multi_zero a i h prevlen) (* update_multi_zero *)
    (fun i acc prevlen1 prevlen2 input1 input2 ->
      if is_sha2 a then
        repeati_associative a acc input1 input2
      else
        update_multi_associative a i acc prevlen1 prevlen2 input1 input2) (* update_multi_associative *)
    (fun _ _ input ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2 in
        sha2_mb_is_incremental a input
      else
        Spec.Hash.Incremental.hash_is_hash_incremental a input)

    (fun _ _ -> ())

    (fun _ _ s ->
      match a with
      | MD5 -> Hacl.Hash.MD5.legacy_init s
      | SHA1 -> Hacl.Hash.SHA1.legacy_init s
      | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> Hacl.SHA2.Scalar32.init #a s
      | SHA3_256 -> Hacl.Hash.SHA3.init_256 s)

    (fun _ s prevlen blocks len ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2.Vec in
        [@inline_let] let blocks_lib = lib_of_buffer #len blocks in
        lib_of_state a s;
        [@inline_let] let state_lib = coerce #(Lib.Buffer.lbuffer Hacl.Spec.SHA2.Vec.(element_t a M32) 8ul) s in
        let h0 = ST.get () in
        live_multi_of_live h0 blocks_lib;
        disjoint_multi_of_disjoint blocks_lib state_lib;
        Hacl.Impl.SHA2.Core.lemma_len_lt_max_a_fits_size_t a len;
        Hacl.SHA2.Scalar32.update_nblocks #a len blocks_lib s;
        Lib.MultiBuffer.loc_multi1 blocks_lib;
        Lib.NTuple.ntup1_lemma #(Lib.Buffer.lbuffer uint8 len) #1 blocks;
        Lib.MultiBuffer.as_seq_multi_lemma h0 blocks_lib 0;
        Lib.NTuple.ntup1_lemma #(multiseq (lanes a M32) (Lib.IntTypes.v len)) #1 (Lib.MultiBuffer.as_seq_multi h0 blocks_lib)
      else
        [@inline_let]
        let update_multi : update_multi_st (|a,()|) =
          match a with
          | MD5 -> Hacl.Hash.MD5.legacy_update_multi
          | SHA1 -> Hacl.Hash.SHA1.legacy_update_multi
          | SHA3_256 -> Hacl.Hash.SHA3.update_multi_256
        in
        update_multi s () blocks (len `U32.div` Hacl.Hash.Definitions.(block_len a)))

    (fun _ s prevlen last last_len ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2.Vec in
        let open Hacl.Impl.SHA2.Generic in
        [@inline_let] let last_lib = lib_of_buffer #last_len last in
        lib_of_state a s;
        [@inline_let] let state_lib = coerce #(Lib.Buffer.lbuffer Hacl.Spec.SHA2.Vec.(element_t a M32) 8ul) s in
        let h0 = ST.get () in
        live_multi_of_live h0 last_lib;
        disjoint_multi_of_disjoint last_lib state_lib;
        Hacl.SHA2.Scalar32.update_last #a (Hacl.Hash.MD.len_add32 a (if a = SHA2_384 || a = SHA2_512 then FStar.Int.Cast.Full.uint64_to_uint128 prevlen else prevlen) last_len) last_len last_lib s;
        Lib.MultiBuffer.loc_multi1 last_lib;
        Lib.NTuple.ntup1_lemma #(Lib.Buffer.lbuffer uint8 last_len) #1 last;
        Lib.MultiBuffer.as_seq_multi_lemma h0 last_lib 0;
        Lib.NTuple.ntup1_lemma #(multiseq (lanes a M32) (Lib.IntTypes.v last_len)) #1 (Lib.MultiBuffer.as_seq_multi h0 last_lib)
      else
        [@inline_let]
        let update_last : update_last_st (|a,()|) =
          match a with
          | MD5 -> Hacl.Hash.MD5.legacy_update_last
          | SHA1 -> Hacl.Hash.SHA1.legacy_update_last
          | SHA3_256 -> Hacl.Hash.SHA3.update_last_256
        in
        [@inline_let]
        let prevlen =
          match a with
          | MD5 | SHA1 -> prevlen
          | SHA3_256 -> ()
        in
        update_last s prevlen last last_len)

    (fun _ _ s dst ->
      if is_sha2 a then
        let open Hacl.Spec.SHA2.Vec in
        let open Hacl.Impl.SHA2.Generic in
        [@inline_let] let dst_lib = lib_of_buffer #(Hacl.Hash.Definitions.hash_len a) dst in
        lib_of_state a s;
        [@inline_let] let state_lib = coerce #(Lib.Buffer.lbuffer Hacl.Spec.SHA2.Vec.(element_t a M32) 8ul) s in
        let h0 = ST.get () in
        live_multi_of_live h0 dst_lib;
        disjoint_multi_of_disjoint dst_lib state_lib;
        Hacl.SHA2.Scalar32.finish #a s dst_lib;
        Lib.MultiBuffer.loc_multi1 dst_lib;
        Lib.NTuple.ntup1_lemma #(Lib.Buffer.lbuffer uint8 (Hacl.Hash.Definitions.hash_len a)) #1 dst;
        let h1 = ST.get () in
        Lib.MultiBuffer.as_seq_multi_lemma h1 dst_lib 0;
        Lib.NTuple.ntup1_lemma #(multiseq (lanes a M32) (hash_length a)) #1 (Lib.MultiBuffer.as_seq_multi h1 dst_lib)
      else
        [@inline_let]
        let finish : finish_st (|a,()|) =
          match a with
          | MD5 -> Hacl.Hash.MD5.legacy_finish
          | SHA1 -> Hacl.Hash.SHA1.legacy_finish
          | SHA3_256 -> Hacl.Hash.SHA3.finish_256
        in
        finish s dst)
#pop-options
