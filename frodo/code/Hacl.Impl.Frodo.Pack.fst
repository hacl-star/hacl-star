module Hacl.Impl.Frodo.Pack

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer
open Lib.Endianness

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.Pack

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -Spec'"

private
val shiftleft_bounds: d:size_nat{d <= 16} ->
  Lemma (
    7 * d < bits U128 /\
    6 * d < bits U128 /\
    5 * d < bits U128 /\
    4 * d < bits U128 /\
    3 * d < bits U128 /\
    2 * d < bits U128 /\
    1 * d < bits U128 /\
    0 * d < bits U128)
let shiftleft_bounds d = ()

inline_for_extraction noextract
val frodo_pack_inner:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t /\ v n2 % 8 = 0}
  -> a:matrix_t n1 n2
  -> d:size_t{v d * v n1 <= max_size_t /\ v n1 * (v n2 / 8) * v d <= max_size_t /\ v d <= 16}
  -> res:lbytes (n1 *! (n2 /. size 8) *! d)
  -> i:size_t{v i < v n1}
  -> Stack unit
    (requires fun h -> live h a /\ live h res /\ disjoint a res)
    (ensures  fun h0 _ h1 ->
      live h1 res /\ modifies (loc_buffer res) h0 h1)
let frodo_pack_inner #n1 #n2 a d res i =
  shiftleft_bounds (v d);
  push_frame();
  let maskd = to_u16 (u32 1 <<. size_to_uint32 d) -. u16 1 in
  let v16 = create #_ #16 (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let h0 = ST.get () in
  let inv h1 (j:nat{j <= v n28}) =
    live h1 res /\
    live h1 v16 /\
    modifies (loc_union (loc_buffer v16) (loc_buffer res)) h0 h1
  in
  let f (j:size_t{v j < v n28}) : Stack unit
    (requires fun h -> inv h (v j))
    (ensures  fun _ _ h2 -> inv h2 (v j + 1)) =
      Lemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
      let start = (i *! n28 +! j) *! d in
      assert_spinoff (v start + v d <= v n1 * (v n2 / 8) * v d);
      let aij0 = a.[i, size 8 *! j +! size 0] &. maskd in
      let aij1 = a.[i, size 8 *! j +! size 1] &. maskd in
      let aij2 = a.[i, size 8 *! j +! size 2] &. maskd in
      let aij3 = a.[i, size 8 *! j +! size 3] &. maskd in
      let aij4 = a.[i, size 8 *! j +! size 4] &. maskd in
      let aij5 = a.[i, size 8 *! j +! size 5] &. maskd in
      let aij6 = a.[i, size 8 *! j +! size 6] &. maskd in
      let aij7 = a.[i, size 8 *! j +! size 7] &. maskd in
      let templong =
           to_u128 aij0 <<. size_to_uint32 (size 7 *! d)
        |. to_u128 aij1 <<. size_to_uint32 (size 6 *! d)
        |. to_u128 aij2 <<. size_to_uint32 (size 5 *! d)
        |. to_u128 aij3 <<. size_to_uint32 (size 4 *! d)
        |. to_u128 aij4 <<. size_to_uint32 (size 3 *! d)
        |. to_u128 aij5 <<. size_to_uint32 (size 2 *! d)
        |. to_u128 aij6 <<. size_to_uint32 (size 1 *! d)
        |. to_u128 aij7 <<. size_to_uint32 (size 0 *! d)
      in
      uint_to_bytes_be v16 templong;
      let src = sub v16 (size 16 -! d) d in // Skips the 1st byte when d = 15
      update_sub res start d src
  in
  Lib.Loops.for (size 0) n28 inv f;
  pop_frame()


val frodo_pack:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t /\ v n2 % 8 = 0}
  -> a:matrix_t n1 n2
  -> d:size_t{v d * v n1 <= max_size_t /\ v n1 * (v n2 / 8) * v d <= max_size_t /\ v d <= 16}
  -> res:lbytes (n1 *! (n2 /. size 8) *! d)
  -> Stack unit
    (requires fun h -> live h a /\ live h res /\ disjoint a res)
    (ensures  fun h0 _ h1 ->
      live h1 res /\
      modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.frodo_pack (as_matrix h0 a) (v d))
let frodo_pack #n1 #n2 a d res =
  let h = ST.get () in
  push_frame();
  let h0 = ST.get () in
  let inv h1 (j:nat{j <= v n1}) =
    live h1 res /\
    modifies (loc_buffer res) h0 h1
  in
  Lib.Loops.for (size 0) n1 inv (frodo_pack_inner a d res);
  pop_frame();
  let h' = ST.get() in
  assume (as_seq h' res == S.frodo_pack (as_matrix h a) (v d))


val frodo_unpack:
    n1:size_t
  -> n2:size_t{v n1 * v n2 <= max_size_t /\ v n2 % 8 = 0}
  -> d:size_t{v d * v n1 <= max_size_t /\ v d * v n1 * v n2 <= max_size_t /\ v d <= 16}
  -> b:lbytes (d *! n1 *! n2 /. size 8)
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h b /\ live h res /\ disjoint b res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.frodo_unpack (v n1) (v n2) (v d) (as_seq h0 b))
[@"c_inline"]
let frodo_unpack n1 n2 d b res =
  // TODO: This proof is fragile. It verifies in interactive mode but not from
  // the command-line. FIX
  admit();
  assert (uint_v (size_to_uint32 d) < bits U32);
  assert (uint_v (size_to_uint32 (size 7 *! d)) < bits U128);
  push_frame();
  let maskd = (u32 1 <<. size_to_uint32 d) -. u32 1 in
  let v16 = create (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let bLen = d *! n1 *! n2 /. size 8 in
  let h0 = ST.get () in
  let inv h1 j =
    live h1 res /\
    live h1 v16 /\
    modifies (loc_union (loc_buffer res) (loc_buffer v16)) h0 h1
  in
  let f' (i:size_t{v i < v n1}): Stack unit
      (requires fun h -> inv h (v i))
      (ensures  fun _ _ h2 -> inv h2 (v i + 1)) =
      let h0 = ST.get () in
      let inv1 h1 j =
        live h1 res /\
        live h1 v16 /\
        modifies (loc_union (loc_buffer res) (loc_buffer v16)) h0 h1
      in
      let f1 (j:size_t{0 <= v j /\ v j < v n28}): Stack unit
        (requires fun h -> inv1 h (v j))
        (ensures  fun _ _ h2 -> inv1 h2 (v j + 1)) =
          assert (v i * v n2 < v n1 * v n2);
          Lemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
          assert (v ((i *! n2 /. size 8 +! j) *! d) + v d <= v bLen);
          let bij = sub #_ #(v bLen) #(v d) b ((i *! n2 /. size 8 +! j) *! d) d in
          copy (sub #_ #_ #(v d) v16 (size 16 -! d) d) d bij;
          let templong = uint_from_bytes_be #U128 v16 in
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) res
          (fun k ->
            let resij = to_u32 (templong >>. size_to_uint32 (size 7 *! d -! d *! k)) &. maskd in
            assert (8 * v j + v k < v n2);
            mset res i (size 8 *! j +! k) (to_u16 resij)
          ) in
      Lib.Loops.for (size 0) n28 inv1 f1 in
  Lib.Loops.for (size 0) n1 inv f';
  pop_frame()
