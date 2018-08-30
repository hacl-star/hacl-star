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
val shift_left_bounds: d:size_nat{d <= 16} ->
  Lemma (
    7 * d < bits U128 /\
    6 * d < bits U128 /\
    5 * d < bits U128 /\
    4 * d < bits U128 /\
    3 * d < bits U128 /\
    2 * d < bits U128 /\
    1 * d < bits U128 /\
    0 * d < bits U128)
let shift_left_bounds d = ()

private
let modifies_popped (#a:Type) (b1:buffer a) (b2:buffer a) (h0:mem) h1 (h2:mem) h3 :
  Lemma
    (requires
      live h0 b1 /\
      fresh_frame h0 h1 /\
      modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2 /\
      get_tip h2 == get_tip h1 /\
      popped h2 h3)
    (ensures live h3 b1)
  [SMTPat (fresh_frame h0 h1); SMTPat (popped h2 h3); SMTPat (live h0 b1);
   SMTPat (modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2)]
= ()


inline_for_extraction noextract
val frodo_pack_inner:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t /\ v n2 % 8 = 0}
  -> a:matrix_t n1 n2
  -> d:size_t{v d * v n1 <= max_size_t /\ v d * v n1 * v n2 <= max_size_t /\ v d <= 16}
  -> res:lbytes (d *! n1 *! n2 /. size 8)
  -> i:size_t{v i < v n1}
  -> Stack unit
    (requires fun h -> live h a /\ live h res /\ disjoint a res)
    (ensures  fun h0 _ h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
let frodo_pack_inner #n1 #n2 a d res i =
  shift_left_bounds (v d);
  push_frame();
  let maskd = to_u16 (u32 1 <<. size_to_uint32 d) -. u16 1 in
  let v16 = create #_ #16 (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let h0 = ST.get () in
  let inv h1 (j:nat{j <= v n28}) =
    live h1 res /\
    live h1 v16 /\
    modifies (loc_union (loc_buffer res) (loc_buffer v16)) h0 h1
  in
  let f (j:size_t{v j < v n28}) : Stack unit
    (requires fun h -> inv h (v j))
    (ensures  fun _ _ h2 -> inv h2 (v j + 1)) =
      Lemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
      let start = (i *! n28 +! j) *! d in
      assert_spinoff (v start + v d <= v d * v n1 * v n2 / 8);
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
  -> d:size_t{v d * v n1 <= max_size_t /\ v d * v n1 * v n2 <= max_size_t /\ v d <= 16}
  -> res:lbytes (d *! n1 *! n2 /. size 8)
  -> Stack unit
    (requires fun h -> live h a /\ live h res /\ disjoint a res)
    (ensures  fun h0 _ h1 ->
      live h1 res /\
      modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.frodo_pack (as_matrix h0 a) (v d))
[@"c_inline"]
let frodo_pack #n1 #n2 a d res =
  let h = ST.get () in
  push_frame();
  let h0 = ST.get () in
  let inv h1 (i:nat{i <= v n1}) =
    live h1 res /\
    modifies (loc_buffer res) h0 h1
  in
  Lib.Loops.for (size 0) n1 inv (frodo_pack_inner a d res);
  pop_frame();
  let h' = ST.get() in
  assume (as_seq h' res == S.frodo_pack (as_matrix h a) (v d))


/// Unpack

inline_for_extraction noextract
val frodo_unpack_inner:
    #n1:size_t
  -> #n2:size_t{v n1 * v n2 <= max_size_t /\ v n2 % 8 = 0}
  -> d:size_t{v d * v n1 <= max_size_t /\ v d * v n1 * v n2 <= max_size_t /\ v d <= 16}
  -> b:lbytes (d *! n1 *! n2 /. size 8)
  -> res:matrix_t n1 n2
  -> i:size_t{v i < v n1}
  -> Stack unit
    (requires fun h -> live h b /\ live h res /\ disjoint b res)
    (ensures  fun h0 _ h1 -> live h1 res /\ modifies (loc_buffer res) h0 h1)
let frodo_unpack_inner #n1 #n2 d b res i =
  shift_left_bounds (v d);
  push_frame();
  let maskd = to_u16 (u32 1 <<. size_to_uint32 d) -. u16 1 in
  let v16 = create #_ #16 (size 16) (u8 0) in
  let n28 = n2 /. size 8 in
  let h0 = ST.get () in
  let inv h1 (j:nat{j <= v n28}) =
    live h1 res /\
    live h1 v16 /\
    modifies (loc_union (loc_buffer res) (loc_buffer v16)) h0 h1
  in
  let f (j:size_t{v j < v n28}) : Stack unit
    (requires fun h -> inv h (v j))
    (ensures  fun _ _ h2 -> inv h2 (v j + 1)) =
      Lemmas.lemma_matrix_index_repeati (v n1) (v n2) (v d) (v i) (v j);
      let start = (i *! n28 +! j) *! d in
      assert_spinoff (v start + v d <= v d * v n1 * v n2 / 8);
      let vij = sub b start d in
      let src = update_sub v16 (size 16 -! d) d vij in
      let templong = uint_from_bytes_be v16 in
      res.[i, size 8 *! j +! size 0] <-
        to_u16 (templong >>. size_to_uint32 (size 7 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 1] <-
        to_u16 (templong >>. size_to_uint32 (size 6 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 2] <-
        to_u16 (templong >>. size_to_uint32 (size 5 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 3] <-
        to_u16 (templong >>. size_to_uint32 (size 4 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 4] <-
        to_u16 (templong >>. size_to_uint32 (size 3 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 5] <-
        to_u16 (templong >>. size_to_uint32 (size 2 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 6] <-
        to_u16 (templong >>. size_to_uint32 (size 1 *! d)) &. maskd;
      res.[i, size 8 *! j +! size 7] <-
        to_u16 (templong >>. size_to_uint32 (size 0 *! d)) &. maskd
  in
  Lib.Loops.for (size 0) n28 inv f;
  pop_frame()


val frodo_unpack:
    n1:size_t
  -> n2:size_t{v n1 * v n2 <= max_size_t /\ v n2 % 8 = 0}
  -> d:size_t{v d * v n1 <= max_size_t /\ v d * v n1 * v n2 <= max_size_t /\ v d <= 16}
  -> b:lbytes (d *! n1 *! n2 /. size 8)
  -> res:matrix_t n1 n2
  -> Stack unit
    (requires fun h -> live h b /\ live h res /\ disjoint b res)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.frodo_unpack #(v n1) #(v n2) (v d) (as_seq h0 b))
[@"c_inline"]
let frodo_unpack n1 n2 d b res =
 let h = ST.get () in
  push_frame();
  let h0 = ST.get () in
  let inv h1 (i:nat{i <= v n1}) =
    live h1 res /\
    modifies (loc_buffer res) h0 h1
  in
  Lib.Loops.for (size 0) n1 inv (frodo_unpack_inner d b res);
  pop_frame();
  let h' = ST.get() in
  assume (as_seq h' res == S.frodo_unpack #(v n1) #(v n2) (v d) (as_seq h' b))
