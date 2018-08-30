module Hacl.Impl.Frodo.Sample

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.PQ.Buffer
open Lib.Endianness

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.Sample
module B = LowStar.Buffer

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val gcmalloc_of_list_pre_eq: #a:Type -> l1:list a -> l2:list a -> Lemma
  (requires gcmalloc_of_list_pre l1 /\ l1 == l2)
  (ensures  gcmalloc_of_list_pre l2)
let gcmalloc_of_list_pre_eq #a l1 l2 = ()

let cdf_table: b:lbuffer uint16 (v cdf_table_len) { LowStar.Buffer.recallable b } =
  gcmalloc_of_list_pre_eq (norm [delta_only [`%cdf_list]] cdf_list) cdf_list;
  LowStar.Buffer.gcmalloc_of_list HyperStack.root cdf_list

inline_for_extraction noextract
val frodo_sample_f:
    t:uint16
  -> i:size_t{v i < v cdf_table_len}
  -> Stack uint16
     (requires fun h -> True)
     (ensures  fun h0 r h1 ->
       modifies loc_none h0 h1 /\ uint_v r == S.frodo_sample_f t (v i))
let frodo_sample_f t i =
  recall cdf_table;
  let ti = cdf_table.(i) in admit();
  to_u16 (to_u32 (ti -. t)) >>. u32 15

inline_for_extraction noextract
val frodo_sample_res:
    sign:uint16{uint_v sign == 0 \/ uint_v sign == 1}
  -> sample:uint16{uint_v sample < v cdf_table_len}
  -> res:uint16{res == S.frodo_sample_res sign (uint_v sample)}
let frodo_sample_res sign sample =
  let res = ((lognot sign +. u16 1) ^. sample) +. sign in
  admit();
  res

#set-options "--max_fuel 1"

val frodo_sample: r:uint16 -> Stack uint16
  (requires fun h -> True)
  (ensures  fun h0 res h1 ->
    modifies loc_none h0 h1 /\ res == S.frodo_sample r)
[@"c_inline"]
let frodo_sample r =
  push_frame();
  let prnd = r >>. u32 1 in
  let sign = r &. u16 1 in
  mod_mask_lemma r (u32 1);
  uintv_extensionality (mod_mask (u32 1)) (u16 1);
  assert (uint_v sign == 0 \/ uint_v sign == 1);

  let sample = create #uint16 #1 (size 1) (u16 0) in
  let h = ST.get () in
  assert (Lib.Sequence.index #_ #1 (as_seq h sample) 0 == u16 0);
  assert (B.get h sample 0 == u16 0);
  let bound = cdf_table_len -! size 1 in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) bound
  (fun h i -> modifies (loc_buffer sample) h0 h /\
    uint_v (B.get h sample 0) == S.frodo_sample_fc prnd i)
  (fun i ->
    let sample0 = sample.(size 0) in
    let samplei = frodo_sample_f prnd i in
    sample.(size 0) <- samplei +. sample0
  );
  let sample0 = sample.(size 0) in
  assert (uint_v sample0 == S.frodo_sample_fc prnd (v bound));
  let res = frodo_sample_res sign sample0 in
  pop_frame();
  res

#set-options "--max_fuel 0"

private
val gen_inv:
    h0:HS.mem
  -> h1:HS.mem
  -> h2:HS.mem
  -> n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t}
  -> r:lbytes (size 2 *! n1 *! n2)
  -> res:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> j:size_nat
  -> Type0
let gen_inv h0 h1 h2 n1 n2 r res i j =
  B.live h2 res /\ B.live h2 r /\ disjoint r res /\
  modifies (loc_buffer res) h1 h2 /\ j <= v n2 /\
  (forall (i0:size_nat{i0 < v i}) (j:size_nat{j < v n2}). get h2 res i0 j == get h1 res i0 j) /\
  (forall (j0:size_nat{j0 < j}). get h2 res (v i) j0 == S.frodo_sample_matrix_fc (v n1) (v n2) (as_seq h0 r) (v i) j0) /\
  (forall (j0:size_nat{j <= j0 /\ j0 < v n2}). get h2 res (v i) j0 == get h0 res (v i) j0) /\
  (forall (i0:size_nat{v i < i0 /\ i0 < v n1}) (j:size_nat{j < v n2}). get h2 res i0 j == get h0 res i0 j) /\
  as_seq h0 r == as_seq h2 r

//TODO: remove once _aseem_monotonic_buffers it's merged
#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract private
val frodo_sample_matrix_fc:
    h0:HS.mem
  -> h1:HS.mem
  -> n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t}
  -> r:lbytes (size 2 *! n1 *! n2)
  -> res0:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> j:size_t{v j < v n2}
  -> Stack unit
    (requires fun h2 -> gen_inv h0 h1 h2 n1 n2 r res0 i (v j))
    (ensures  fun _ _ h2 -> gen_inv h0 h1 h2 n1 n2 r res0 i (v j + 1))
let frodo_sample_matrix_fc h0 h1 n1 n2 r res0 i j =
  Lemmas.lemma_matrix_index_repeati1 (v n1) (v n2) (v i) (v j);
  let resij = uint_from_bytes_le (sub #_ #_ #2 r (size 2 *! (n2 *! i +! j)) (size 2)) in
  mset res0 i j (frodo_sample resij)

private
val sample_inner_inv:
    h0:HS.mem
  -> h1:HS.mem
  -> n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t}
  -> r:lbytes (size 2 *! n1 *! n2)
  -> res:matrix_t n1 n2
  -> i:size_nat{i <= v n1}
  -> Type0
let sample_inner_inv h0 h1 n1 n2 r res i =
  B.live h1 r /\ B.live h1 res /\ disjoint r res /\
  modifies (loc_buffer res) h0 h1 /\ as_seq h0 r == as_seq h1 r /\
  (forall (i0:size_nat{i0 < i}) (j:size_nat{j < v n2}). get h1 res i0 j == S.frodo_sample_matrix_fc (v n1) (v n2) (as_seq h0 r) i0 j) /\
  (forall (i0:size_nat{i <= i0 /\ i0 < v n1}) (j:size_nat{j < v n2}). get h1 res i0 j == get h0 res i0 j)

val frodo_sample_matrix:
    n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> ctr:uint16
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 r h1 ->
      live h1 res /\ modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_sample_matrix (v n1) (v n2) (v seed_len) (as_seq h0 seed) ctr)
[@"c_inline"]
let frodo_sample_matrix n1 n2 seed_len seed ctr res =
  push_frame();
  let r = create (size 2 *! n1 *! n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *! n1 *! n2) r;
  let h0 = ST.get () in
  Lib.Loops.for (size 0) n1
    (fun h1 i -> sample_inner_inv h0 h1 n1 n2 r res i)
    (fun i ->
      let h1 = ST.get () in
      Lib.Loops.for (size 0) n2
      (fun h2 j -> gen_inv h0 h1 h2 n1 n2 r res i j)
      (fun j ->
        Lemmas.lemma_matrix_index_repeati1 (v n1) (v n2) (v i) (v j);
        let resij = sub r (size 2 *! (n2 *! i +! j)) (size 2) in
        mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
      )
    );
  pop_frame();
  let h1 = ST.get () in
  Spec.Matrix.extensionality (as_matrix h1 res) (S.frodo_sample_matrix (v n1) (v n2) (v seed_len) (as_seq h0 seed) ctr)
