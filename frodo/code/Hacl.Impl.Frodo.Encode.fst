module Hacl.Impl.Frodo.Encode

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.PQ.Lib
open Hacl.Impl.Frodo.Params

open LowStar.ModifiesPat
open LowStar.Modifies

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module FLemmas = Spec.Frodo.Lemmas
module S = Spec.Frodo.Encode

#reset-options "--z3rlimit 50 --max_fuel 0"
val ec:
    b:size_t{v b < v params_logq}
  -> k:uint16{uint_v k < pow2 (v b)}
  -> r:uint16{r == S.ec (v b) k}
  [@ "substitute"]
let ec b a =
  a <<. (size_to_uint32 (params_logq -. b))

val dc:
    b:size_t{v b < v params_logq}
  -> c:uint16
  -> r:uint16{r == S.dc (v b) c}
  [@ "substitute"]
let dc b c =
  let res1 = (c +. (u16 1 <<. size_to_uint32 (params_logq -. b -. size 1))) >>. size_to_uint32 (params_logq -. b) in
  res1 &. ((u16 1 <<. size_to_uint32 b) -. u16 1)

val frodo_key_encode:
    b:size_t{v b <= 8}
  -> a:lbytes ((params_nbar *! params_nbar *! b) /. size 8)
  -> res:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires (fun h -> B.live h a /\ B.live h res /\ B.disjoint a res))
    (ensures (fun h0 _ h1 -> B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_key_encode (v b) (B.as_seq h0 a)))
[@"c_inline"]
let frodo_key_encode b a res =
  push_frame();
  let n2 = params_nbar /. size 8 in
  let aLen = (params_nbar *! params_nbar *! b) /. size 8 in
  let v8 = create (size 8) (u8 0) in
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v params_nbar}) =
    B.live h1 res /\ B.live h1 v8 /\ modifies (loc_union (loc_buffer res) (loc_buffer v8)) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v params_nbar}): Stack unit
      (requires (fun h -> inv h (v i)))
      (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let h0 = ST.get () in
      let inv1 (h1:mem) (j:nat{j <= v n2}) =
        B.live h1 res /\ B.live h1 v8 /\ modifies (loc_union (loc_buffer res) (loc_buffer v8)) h0 h1 in
      let f1 (j:size_t{0 <= v j /\ v j < v n2}): Stack unit
        (requires (fun h -> inv1 h (v j)))
        (ensures (fun _ _ h2 -> inv1 h2 (v j + 1))) =
          copy (sub v8 (size 0) b) b (sub #uint8 #(v aLen) #(v b) a ((i +! j) *! b) b);
          let vij = uint_from_bytes_le #U64 v8 in
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) res
          (fun k ->
            let ak = (vij >>. size_to_uint32 (b *! k)) &. ((u64 1 <<. size_to_uint32 b) -. u64 1) in
            mset res i (size 8 *! j +! k) (ec b (to_u16 ak))
          ) in

      Lib.Loops.for (size 0) n2 inv1 f1 in
  Lib.Loops.for (size 0) params_nbar inv f';
  pop_frame()

val frodo_key_decode:
  b:size_t{v b <= 8} ->
  a:matrix_t params_nbar params_nbar ->
  res:lbytes ((params_nbar *! params_nbar *! b) /. size 8) -> Stack unit
  (requires (fun h -> B.live h a /\ B.live h res /\ B.disjoint a res))
  (ensures (fun h0 r h1 -> B.live h1 res /\ modifies (loc_buffer res) h0 h1))
  [@"c_inline"]
let frodo_key_decode b a res =
  push_frame();
  let n2 = params_nbar /. size 8 in
  let resLen = (params_nbar *! params_nbar *! b) /. size 8 in
  let v8 = create (size 8) (u8 0) in
  let templong:lbuffer uint64 1 = create (size 1) (u64 0) in
  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v params_nbar}) =
    B.live h1 res /\ B.live h1 v8 /\ B.live h1 templong /\
    modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v8) (loc_buffer templong))) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v params_nbar}): Stack unit
      (requires (fun h -> inv h (v i)))
      (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      let h0 = ST.get () in
      let inv1 (h1:mem) (j:nat{j <= v n2}) =
        B.live h1 res /\ B.live h1 v8 /\ B.live h1 templong /\
        modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v8) (loc_buffer templong))) h0 h1 in
      let f1 (j:size_t{0 <= v j /\ v j < v n2}): Stack unit
        (requires (fun h -> inv1 h (v j)))
        (ensures (fun _ _ h2 -> inv1 h2 (v j + 1))) =
          templong.(size 0) <- u64 0;
          let h1 = ST.get () in
          loop_nospec #h1 (size 8) templong
          (fun k ->
            let aijk = mget a i (size 8 *! j +! k) in
            let aij = dc b aijk in
            templong.(size 0) <- templong.(size 0) |. (to_u64 aij <<. size_to_uint32 (b *! k))
          );
          uint_to_bytes_le #U64 v8 (templong.(size 0));
          copy (sub res ((i +! j) *! b) b) b (sub #uint8 #8 #(v b) v8 (size 0) b) in

      Lib.Loops.for (size 0) n2 inv1 f1 in
  Lib.Loops.for (size 0) params_nbar inv f';
  pop_frame()
