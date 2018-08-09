module Hacl.Impl.Frodo.Pack

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module ST = FStar.HyperStack.ST
module Lemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_pack:
    n1:size_t
  -> n2:size_t{v n1 * v n2 < max_size_t /\ v n2 % 8 = 0}
  -> a:matrix_t n1 n2
  -> d:size_t{v d * v n1 < max_size_t /\ v d * v n1 * v n2 < max_size_t /\ v d <= 16}
  -> res:lbytes (d *! n1 *! n2 /. size 8)
  -> Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint a res)
  (ensures  fun h0 r h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let frodo_pack n1 n2 a d res =
  assert (uint_v (size_to_uint32 d) < bits U32);
  assert (uint_v (size_to_uint32 (size 7 *! d)) < bits U128);
  push_frame();
  let maskd = (u32 1 <<. size_to_uint32 d) -. u32 1 in
  let templong:lbuffer uint128 1 = create (size 1) (to_u128 (u64 0)) in
  let v16 = create #_ #16 (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let resLen = d *! n1 *! n2 /. size 8 in
  let h0 = ST.get () in
  let inv h1 j =
    live h1 res /\
    live h1 v16 /\
    live h1 templong /\
    modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v16) (loc_buffer templong))) h0 h1
  in
  let f' (i:size_t{0 <= v i /\ v i < v n1}): Stack unit
      (requires fun h -> inv h (v i))
      (ensures  fun _ _ h2 -> inv h2 (v i + 1)) =
      let h0 = ST.get () in
      let inv1 h1 j =
        live h1 res /\
        live h1 v16 /\
        live h1 templong /\
        modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v16) (loc_buffer templong))) h0 h1
      in
      let f1 (j:size_t{0 <= v j /\ v j < v n28}): Stack unit
        (requires fun h -> inv1 h (v j))
        (ensures  fun _ _ h2 -> inv1 h2 (v j + 1)) =
          templong.(size 0) <- to_u128 (u64 0);
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) templong
          (fun k ->
            assert (8 * v j + v k < v n2);
            let aij = to_u32 (mget a i (size 8 *! j +! k)) &. maskd in
            templong.(size 0) <- templong.(size 0) |. (to_u128 aij <<. size_to_uint32 (size 7 *! d -! d *! k))
          );
          uint_to_bytes_be #U128 v16 (templong.(size 0));
	  Lemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
	  assert (((v i * v n2 / 8 + v j) * v d) + v d <= v resLen);
          copy (sub res ((i *! n2 /. size 8 +! j) *! d) d) d
               (sub #uint8 #16 #(v d) v16 (size 16 -! d) d)
      in
      Lib.Loops.for (size 0) n28 inv1 f1 in
  Lib.Loops.for (size 0) n1 inv f';
  pop_frame()


#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val frodo_unpack:
    n1:size_t
  -> n2:size_t{v n1 * v n2 < max_size_t /\ v n2 % 8 = 0}
  -> d:size_t{v d * v n1 < max_size_t /\ v d * v n1 * v n2 < max_size_t /\ v d <= 16
    /\ uint_v (size_to_uint32 d) < bits U32 
    /\ uint_v (size_to_uint32 (size 7 *! d)) < bits U128}
  -> b:lbytes (d *! n1 *! n2 /. size 8)
  -> res:matrix_t n1 n2
  -> Stack unit
  (requires fun h -> live h b /\ live h res /\ disjoint b res)
  (ensures  fun h0 r h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let frodo_unpack n1 n2 d b res =
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
