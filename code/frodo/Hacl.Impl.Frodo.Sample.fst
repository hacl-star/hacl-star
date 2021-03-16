module Hacl.Impl.Frodo.Sample

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.Sample
module FP = Spec.Frodo.Params

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val frodo_sample_f:
    a:FP.frodo_alg
  -> t:uint16{uint_v t < pow2 15}
  -> i:size_t{v i < v (cdf_table_len a)}
  -> Stack uint16
    (requires fun h -> True)
    (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
      v r == S.frodo_sample_f a t (v i))

let frodo_sample_f a t i =
  recall_contents (cdf_table a) (FP.cdf_table a);
  let ti = index (cdf_table a) i in
  FP.lemma_cdf_list a (v i);
  Lemmas.lemma_frodo_sample t ti;
  to_u16 (to_u32 (ti -. t)) >>. 15ul


inline_for_extraction noextract
val frodo_sample_res:
    a:FP.frodo_alg
  -> sign:uint16{v sign <= 1}
  -> sample:uint16{v sample < v (cdf_table_len a)}
  -> res:uint16{res == S.frodo_sample_res a sign (v sample)}

let frodo_sample_res a sign sample =
  Lemmas.lemma_frodo_sample2 sign sample;
  ((lognot sign +. u16 1) ^. sample) +. sign


inline_for_extraction noextract
let frodo_sample_st (a:FP.frodo_alg) =
    r:uint16
  -> Stack uint16
    (requires fun h -> True)
    (ensures  fun h0 res h1 -> modifies0 h0 h1 /\
      res == S.frodo_sample a r)


#push-options "--fuel 1"
inline_for_extraction noextract
val frodo_sample: a:FP.frodo_alg -> frodo_sample_st a
let frodo_sample a r =
  push_frame();
  let prnd = r >>. 1ul in
  let sign = r &. u16 1 in
  mod_mask_lemma r 1ul;
  assert (v #U16 #SEC (mod_mask 1ul) == 1);
  assert (v sign == 0 \/ v sign == 1);

  let sample :lbuffer uint16 1ul = create (size 1) (u16 0) in
  let h = ST.get () in
  assert (LSeq.index #_ #1 (as_seq h sample) 0 == u16 0);
  assert (bget h sample 0 == u16 0);
  let bound = cdf_table_len a -! 1ul in
  let h0 = ST.get () in
  Lib.Loops.for 0ul bound
  (fun h i ->
    modifies1 sample h0 h /\
    v (bget h sample 0) == S.frodo_sample_fc a prnd i)
  (fun i ->
   let sample0 = sample.(0ul) in
   let samplei = frodo_sample_f a prnd i in
   sample.(0ul) <- samplei +. sample0
  );
  let sample0 = sample.(0ul) in
  assert (v sample0 == S.frodo_sample_fc a prnd (v bound));
  let res = frodo_sample_res a sign sample0 in
  pop_frame();
  res
#pop-options


inline_for_extraction noextract
val frodo_sample_matrix1:
    a:FP.frodo_alg
  -> frodo_sample:frodo_sample_st a
  -> n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 <= max_size_t}
  -> r:lbuffer uint8 (size 2 *! n1 *! n2)
  -> i:size_t{v i < v n1}
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h ->
      live h r /\ live h res /\ disjoint r res)
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res ==
      S.frodo_sample_matrix1 a (v n1) (v n2) (as_seq h0 r) (v i) (as_matrix h0 res))

let frodo_sample_matrix1 a frodo_sample n1 n2 r i res =
  [@ inline_let]
  let spec h0 = S.frodo_sample_matrix0 a (v n1) (v n2) (as_seq h0 r) (v i) in
  let h0 = ST.get () in
  loop1 h0 n2 res spec
  (fun j ->
    Loops.unfold_repeati (v n2) (spec h0) (as_seq h0 res) (v j);
    Lemmas.lemma_matrix_index_repeati1 (v n1) (v n2) (v i) (v j);
    let resij = sub r (size 2 *! (n2 *! i +! j)) (size 2) in
    mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
  )


inline_for_extraction noextract
let frodo_sample_matrix_st (a:FP.frodo_alg) =
    n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 <= max_size_t}
  -> r:lbytes (2ul *! n1 *! n2)
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h ->
      live h r /\ live h res /\ disjoint r res)
    (ensures  fun h0 r_ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res == S.frodo_sample_matrix a (v n1) (v n2) (as_seq h0 r))


inline_for_extraction noextract
val frodo_sample_matrix_:
    a:FP.frodo_alg
  -> frodo_sample:frodo_sample_st a
  -> frodo_sample_matrix_st a

let frodo_sample_matrix_ a frodo_sample n1 n2 r res =
  memset res (u16 0) (n1 *! n2);
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v n1 * v n2)) (as_seq h0 res);

  [@ inline_let]
  let spec h0 = S.frodo_sample_matrix1 a (v n1) (v n2) (as_seq h0 r) in
  loop1 h0 n1 res spec
  (fun i ->
    Loops.unfold_repeati (v n1) (spec h0) (as_seq h0 res) (v i);
    frodo_sample_matrix1 a frodo_sample n1 n2 r i res
  )


[@CInline]
let frodo_sample_matrix64 : frodo_sample_matrix_st FP.Frodo64 =
  frodo_sample_matrix_ FP.Frodo64 (frodo_sample FP.Frodo64)
[@CInline]
let frodo_sample_matrix640 : frodo_sample_matrix_st FP.Frodo640 =
  frodo_sample_matrix_ FP.Frodo640 (frodo_sample FP.Frodo640)
[@CInline]
let frodo_sample_matrix976 : frodo_sample_matrix_st FP.Frodo976 =
  frodo_sample_matrix_ FP.Frodo976 (frodo_sample FP.Frodo976)
[@CInline]
let frodo_sample_matrix1344 : frodo_sample_matrix_st FP.Frodo1344=
  frodo_sample_matrix_ FP.Frodo1344 (frodo_sample FP.Frodo1344)

inline_for_extraction noextract
let frodo_sample_matrix (a:FP.frodo_alg) : frodo_sample_matrix_st a =
  match a with
  | FP.Frodo64 -> frodo_sample_matrix64
  | FP.Frodo640 -> frodo_sample_matrix640
  | FP.Frodo976 -> frodo_sample_matrix976
  | FP.Frodo1344 -> frodo_sample_matrix1344
