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
module Lemmas = Spec.Frodo.Lemmas
module Seq = Lib.Sequence
module S = Spec.Frodo.Sample

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let cdf_seq: Seq.lseq uint16 (v cdf_table_len) = 
  assert_norm (List.Tot.length cdf_list == v cdf_table_len);
  Seq.of_list cdf_list

let cdf_table: b:ilbuffer uint16 cdf_table_len{recallable b /\ witnessed b cdf_seq} = 
  createL_global cdf_list

inline_for_extraction noextract
val frodo_sample_f:
    t:uint16{uint_v t < pow2 15}
  -> i:size_t{v i < v cdf_table_len}
  -> Stack uint16
     (requires fun h -> True)
     (ensures  fun h0 r h1 -> modifies0 h0 h1 /\ uint_v r == S.frodo_sample_f t (v i))
let frodo_sample_f t i =
  assert_norm (List.Tot.length cdf_list <= max_size_t);
  recall_contents cdf_table cdf_seq;
  let ti = index cdf_table (Lib.RawIntTypes.size_to_UInt32 i) in
  S.lemma_frodo_sample0 (v i);
  S.lemma_frodo_sample1 t ti;
  to_u16 (to_u32 (ti -. t)) >>. 15ul

inline_for_extraction noextract
val frodo_sample_res:
    sign:uint16{uint_v sign == 0 \/ uint_v sign == 1}
  -> sample:uint16{uint_v sample < v cdf_table_len}
  -> res:uint16{res == S.frodo_sample_res sign (uint_v sample)}
let frodo_sample_res sign sample =
  Lemmas.lemma_frodo_sample2 sign sample;
  ((lognot sign +. u16 1) ^. sample) +. sign

#set-options "--max_fuel 1"

val frodo_sample: r:uint16 -> Stack uint16
  (requires fun h -> True)
  (ensures  fun h0 res h1 -> modifies0 h0 h1 /\ res == S.frodo_sample r)
[@"c_inline"]
let frodo_sample r =
  push_frame();
  let prnd = r >>. 1ul in
  let sign = r &. u16 1 in
  mod_mask_lemma r 1ul;
  assert (v #U16 #SEC (mod_mask 1ul) == 1);
  assert (uint_v sign == 0 \/ uint_v sign == 1);
  let sample :lbuffer uint16 1ul = create (size 1) (u16 0) in
  let h = ST.get () in
  assert (Seq.index #_ #1 (as_seq h sample) 0 == u16 0);
  assert (bget h sample 0 == u16 0);
  let bound = cdf_table_len -! 1ul in
  let h0 = ST.get () in
  Lib.Loops.for 0ul bound
  (fun h i -> modifies1 sample h0 h /\ v (bget h sample 0) == S.frodo_sample_fc prnd i)
  (fun i ->
   let sample0 = sample.(0ul) in
   let samplei = frodo_sample_f prnd i in
   sample.(0ul) <- samplei +. sample0
  );
  let sample0 = sample.(0ul) in
  assert (uint_v sample0 == S.frodo_sample_fc prnd (v bound));
  let res = frodo_sample_res sign sample0 in
  pop_frame();
  res

#set-options "--max_fuel 0"

inline_for_extraction noextract
val frodo_sample_matrix1:
    n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 <= max_size_t}
  -> r:lbuffer uint8 (size 2 *! n1 *! n2)
  -> i:size_t{v i < v n1}
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h r /\ live h res /\ disjoint r res)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_matrix h1 res ==
      S.frodo_sample_matrix1 (v n1) (v n2) (as_seq h0 r) (v i) (as_matrix h0 res))
let frodo_sample_matrix1 n1 n2 r i res =
  [@ inline_let]
  let spec h0 = S.frodo_sample_matrix0 (v n1) (v n2) (as_seq h0 r) (v i) in
  let h0 = ST.get () in
  loop1 h0 n2 res spec
  (fun j ->
    Lib.LoopCombinators.unfold_repeati (v n2) (spec h0) (as_seq h0 res) (v j);
    Lemmas.lemma_matrix_index_repeati1 (v n1) (v n2) (v i) (v j);
    let resij = sub r (size 2 *! (n2 *! i +! j)) (size 2) in
    mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
  )

val frodo_sample_matrix:
    n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 <= max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> ctr:uint16
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 r h1 ->
      live h1 res /\ modifies1 res h0 h1 /\
      as_matrix h1 res ==
      S.frodo_sample_matrix (v n1) (v n2) (v seed_len) (as_seq h0 seed) ctr)
[@"c_inline"]
let frodo_sample_matrix n1 n2 seed_len seed ctr res =
  push_frame();
  let r = create (2ul *! n1 *! n2) (u8 0) in
  cshake_frodo seed_len seed ctr (2ul *! n1 *! n2) r;
  memset res (u16 0) (n1 *! n2);
  let h0 = ST.get () in
  Seq.eq_intro (Seq.sub (as_seq h0 res) 0 (v n1 * v n2)) (as_seq h0 res);
  [@ inline_let]
  let spec h0 = S.frodo_sample_matrix1 (v n1) (v n2) (as_seq h0 r) in
  let h0 = ST.get () in
  loop1 h0 n1 res spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v n1) (spec h0) (as_seq h0 res) (v i);
    frodo_sample_matrix1 n1 n2 r i res
  );
  pop_frame ()
