module Hacl.Impl.Frodo.Sample

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer
open LowStar.BufferOps

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.PQ.Lib
open Hacl.Keccak
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

let cshake_frodo = cshake128_frodo

val frodo_sample: r:uint16 -> Stack uint16
  (requires fun h -> True)
  (ensures  fun h0 r h1 -> modifies loc_none h0 h1)
[@"c_inline"]
let frodo_sample r =
  push_frame();
  let prnd = r >>. u32 1 in
  let sign = r &. u16 1 in
  let sample = create #uint16 #1 (size 1) (u16 0) in
  let h0 = ST.get () in
  let bound = cdf_table_len -! size 1 in
  loop_nospec #h0 bound sample
  (fun j ->
    recall cdf_table;
    let tj = cdf_table.(j) in
    let sample0 = sample.(size 0) in
    sample.(size 0) <- sample0 +. (to_u16 (to_u32 (tj -. prnd)) >>. u32 15)
  );
  let sample0 = sample.(size 0) in
  let res = ((lognot sign +. u16 1) ^. sample0) +. sign in
  pop_frame();
  res

val frodo_sample_matrix:
    n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> ctr:uint16
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 r h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let frodo_sample_matrix n1 n2 seed_len seed ctr res =
  push_frame();
  let r = create (size 2 *! n1 *! n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *! n1 *! n2) r;
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h0 = ST.get () in
    loop_nospec #h0 n2 res
    (fun j ->
      Lemmas.lemma_matrix_index_repeati1 (v n1) (v n2) (v i) (v j);
      let resij = sub r (size 2 *! (n2 *! i +! j)) (size 2) in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
    )
  );
  pop_frame()

val frodo_sample_matrix_tr:
    n1:size_t
  -> n2:size_t{0 < 2 * v n1 * v n2 /\ 2 * v n1 * v n2 < max_size_t}
  -> seed_len:size_t{v seed_len > 0}
  -> seed:lbytes seed_len
  -> ctr:uint16
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h seed /\ live h res /\ disjoint seed res)
    (ensures  fun h0 r h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let frodo_sample_matrix_tr n1 n2 seed_len seed ctr res =
  push_frame();
  let r = create (size 2 *! n1 *! n2) (u8 0) in
  cshake_frodo seed_len seed ctr (size 2 *! n1 *! n2) r;
  let h0 = ST.get () in
  loop_nospec #h0 n1 res
  (fun i ->
    let h0 = ST.get () in
    loop_nospec #h0 n2 res
    (fun j ->
      Lemmas.lemma_matrix_index_repeati2 (v n1) (v n2) (v i) (v j);
      let resij = sub r (size 2 *! (n1 *! j +! i)) (size 2) in
      mset res i j (frodo_sample (uint_from_bytes_le #U16 resij))
    )
  );
  pop_frame()
