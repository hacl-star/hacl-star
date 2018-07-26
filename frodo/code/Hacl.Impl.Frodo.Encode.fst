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

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST

module LSeq = Lib.Sequence
module M    = Spec.Matrix
module S    = Spec.Frodo.Encode
module FLemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0"

inline_for_extraction noextract private
val ec:
    b:size_t{v b < v params_logq}
  -> k:uint16{uint_v k < pow2 (v b)}
  -> r:uint16{r == S.ec (v b) k}
let ec b a =
  a <<. (size_to_uint32 (params_logq -. b))

inline_for_extraction noextract private
val dc:
    b:size_t{v b < v params_logq}
  -> c:uint16
  -> r:uint16{r == S.dc (v b) c}
let dc b c =
  let res1 = (c +. (u16 1 <<. size_to_uint32 (params_logq -. b -. size 1))) >>. size_to_uint32 (params_logq -. b) in
  res1 &. ((u16 1 <<. size_to_uint32 b) -. u16 1)

inline_for_extraction noextract private
val ec1:
    b:size_t{v b <= 8}
  -> vij:uint64
  -> k:size_t{v k < 8}
  -> res:uint16{res == S.ec1 (v b) vij (v k)}
let ec1 b vij k =
  FLemmas.modulo_pow2_u64 (vij >>. size_to_uint32 (b *! k)) (v b);
  let rk = (vij >>. size_to_uint32 (b *! k)) &. ((u64 1 <<. size_to_uint32 b) -. u64 1) in
  ec b (to_u16 rk)

inline_for_extraction noextract private
val frodo_key_encode1:
    b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res0:matrix_t params_nbar params_nbar
  -> vij:uint64
  -> i:size_t{v i < v params_nbar}
  -> j:size_t{v j < v params_nbar / 8}
  -> Stack unit
    (requires fun h ->
      B.live h a /\ B.live h res0 /\ B.disjoint a res0)
    (ensures fun h0 _ h1 -> B.live h1 res0 /\ modifies (loc_buffer res0) h0 h1 /\
      as_matrix h1 res0 == S.frodo_key_encode1 (v b) (B.as_seq h0 a) (as_matrix h0 res0) vij (v i) (v j))
let frodo_key_encode1 b a res0 vij i j =
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 8)
  (fun h1 k ->
    B.live h1 res0 /\ B.live h1 a /\ modifies (loc_buffer res0) h0 h1 /\
    (forall (i0:size_nat{i0 < v params_nbar /\ i0 <> v i}) (j:size_nat{j < v params_nbar / 8}) (k:size_nat{k < 8}).
      get h1 res0 i0 (8 * j + k) == get h0 res0 i0 (8 * j + k)) /\
    (forall (k1:size_nat{k1 < k}). get h1 res0 (v i) (8 * v j + k1) == S.ec1 (v b) vij k1) /\
    (forall (k1:size_nat{k <= k1 /\ k1 < 8}). get h1 res0 (v i) (8 * v j + k1) == get h0 res0 (v i) (8 * v j + k1)))
  (fun k ->
    mset res0 i (size 8 *! j +! k) (ec1 b vij k)
  );
  let h2 = ST.get () in
  S.lemma_matrix_equality_nbar (as_matrix h2 res0) (S.frodo_key_encode1 (v b) (B.as_seq h0 a) (as_matrix h0 res0) vij (v i) (v j))

inline_for_extraction noextract private
val frodo_key_encode2:
    b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res0:matrix_t params_nbar params_nbar
  -> v8:lbytes (size 8)
  -> i:size_t{v i < v params_nbar}
  -> j:size_t{v j < v params_nbar / 8}
  -> Stack unit
    (requires fun h ->
      B.live h v8 /\ B.live h a /\ B.live h res0 /\
      B.disjoint a res0 /\ B.disjoint v8 a /\ B.disjoint v8 res0 /\
      (forall (k:size_nat{v b <= k /\ k < 8}). LSeq.index #uint8 #8 (B.as_seq h v8) k == u8 0))
    (ensures  fun h0 _ h1 -> B.live h1 res0 /\ modifies (loc_union (loc_buffer res0) (loc_buffer v8)) h0 h1 /\
      (forall (k:size_nat{v b <= k /\ k < 8}). LSeq.index #uint8 #8 (B.as_seq h1 v8) k == u8 0) /\
      as_matrix h1 res0 == S.frodo_key_encode2 (v b) (B.as_seq h0 a) (as_matrix h0 res0) (B.as_seq h0 v8) (v i) (v j))
let frodo_key_encode2 b a res0 v8 i j =
  let aLen = params_nbar *! params_nbar *! b /. size 8 in
  update_sub v8 (size 0) b (sub #_ #_ #(v b) a ((i +! j) *! b) b);
  let vij = uint_from_bytes_le #U64 v8 in
  frodo_key_encode1 b a res0 vij i j

val frodo_key_encode:
    b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h res /\ B.disjoint a res)
    (ensures  fun h0 _ h1 -> B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_key_encode (v b) (B.as_seq h0 a))
[@"c_inline"]
let frodo_key_encode b a res =
  push_frame();
  let v8 = create (size 8) (u8 0) in
  let n2 = params_nbar /. size 8 in

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
	  frodo_key_encode2 b a res v8 i j in

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
