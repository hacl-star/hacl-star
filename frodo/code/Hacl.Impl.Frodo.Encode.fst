module Hacl.Impl.Frodo.Encode

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.ModifiesPat
open LowStar.Modifies

open Lib.IntTypes
open Lib.PQ.Buffer

open Hacl.Impl.PQ.Lib
open Hacl.Impl.Frodo.Params

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module LSeq = Lib.Sequence
module M    = Spec.Matrix
module S    = Spec.Frodo.Encode
module FLemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

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
    (ensures fun h0 _ h1 ->
      B.live h1 res0 /\ modifies (loc_buffer res0) h0 h1 /\
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
  -> i:size_t{v i < v params_nbar}
  -> j:size_t{v j < v params_nbar / 8}
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h res0 /\ B.disjoint a res0)
    (ensures  fun h0 _ h1 ->
      B.live h1 a /\ B.live h1 res0 /\
      modifies (loc_buffer res0) h0 h1 /\
      as_matrix h1 res0 == S.frodo_key_encode2 (v b) (B.as_seq h0 a) (as_matrix h0 res0) (v i) (v j))
let frodo_key_encode2 b a res0 i j =
  push_frame();
  let v8 = create (size 8) (u8 0) in
  let aLen = params_nbar *! params_nbar *! b /. size 8 in
  update_sub v8 (size 0) b (sub #_ #_ #(v b) a ((i +! j) *! b) b);
  let vij = uint_from_bytes_le #U64 v8 in
  frodo_key_encode1 b a res0 vij i j;
  pop_frame()

inline_for_extraction noextract private
val frodo_key_encode_inner_inv:
    h0:HS.mem
  -> h1:HS.mem
  -> h2:HS.mem
  -> b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res:matrix_t params_nbar params_nbar
  -> i:size_t{v i < v params_nbar}
  -> j:size_nat
  -> Type0
let frodo_key_encode_inner_inv h0 h1 h2 b a res i j =
  let n2 = params_nbar /. size 8 in
  j <= v n2 /\
  B.live h2 res /\ B.live h2 a /\ B.disjoint a res /\
  modifies (loc_buffer res) h1 h2 /\
  (forall (i0:size_nat{i0 < v i}) (j:size_nat{j < v n2}) (k:size_nat{k < 8}). get h2 res i0 (8 * j + k) == get h1 res i0 (8 * j + k)) /\
  (forall (j0:size_nat{j0 < j}) (k:size_nat{k < 8}). get h2 res (v i) (8 * j0 + k) == S.frodo_key_encode_inner (v b) (B.as_seq h0 a) (v i) j0 k) /\
  (forall (j0:size_nat{j <= j0 /\ j0 < v n2}) (k:size_nat{k < 8}). get h2 res (v i) (8 * j0 + k) == get h0 res (v i) (8 * j0 + k)) /\
  (forall (i0:size_nat{v i < i0 /\ i0 < v params_nbar}) (j:size_nat{j < v n2}) (k:size_nat{k < 8}). get h2 res i0 (8 * j + k) == get h0 res i0 (8 * j + k)) /\
  B.as_seq h2 a == B.as_seq h0 a

inline_for_extraction noextract private
val frodo_key_encode_inner:
    h0:HS.mem
  -> h1:HS.mem
  -> b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res:matrix_t params_nbar params_nbar
  -> i:size_t{v i < v params_nbar}
  -> j:size_t{v j < v params_nbar / 8}
  -> Stack unit
    (requires fun h2 -> frodo_key_encode_inner_inv h0 h1 h2 b a res i (v j))
    (ensures  fun _ _ h2 -> frodo_key_encode_inner_inv h0 h1 h2 b a res i (v j + 1))
let frodo_key_encode_inner h0 h1 b a res i j =
  assert (forall (k:size_nat{k < 8}).
    M.mget (S.frodo_key_encode2 (v b) (B.as_seq h0 a) (as_matrix h0 res) (v i) (v j)) (v i) (8 * v j + k) ==
    S.frodo_key_encode_inner (v b) (B.as_seq h0 a) (v i) (v j) k);
  let h1 = ST.get () in
  frodo_key_encode2 b a res i j;
  let h2 = ST.get () in
  assert (forall (k:size_nat{k < 8}). get h2 res (v i) (8 * v j + k) == S.frodo_key_encode_inner (v b) (B.as_seq h0 a) (v i) (v j) k)

//TODO:move to Lemmas
private
val onemore: p:(nat -> Type0) -> q:(i:nat{p i} -> Type0) -> b:nat{p b} -> Lemma
  (requires (forall (i:nat{p i /\ i < b}). q i) /\ q b)
  (ensures  forall (i:nat{p i /\ i <= b}). q i)
let onemore p q b = ()

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
  let n2 = params_nbar /. size 8 in

  let h0 = ST.get () in
  Lib.Loops.for (size 0) params_nbar
  (fun h1 i ->
    B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
    (forall (i0:size_nat{i0 < i}) (j:size_nat{j < v n2}) (k:size_nat{k < 8}).
      get h1 res i0 (8 * j + k) == S.frodo_key_encode_inner (v b) (B.as_seq h0 a) i0 j k) /\
    (forall (i0:size_nat{i <= i0 /\ i0 < v params_nbar}) (j:size_nat{j < v n2}) (k:size_nat{k < 8}).
      get h1 res i0 (8 * j + k) == get h0 res i0 (8 * j + k)))
  (fun i ->
    let h1 = ST.get () in
    Lib.Loops.for (size 0) n2
    (fun h2 j -> frodo_key_encode_inner_inv h0 h1 h2 b a res i j)
    (fun j -> frodo_key_encode_inner h0 h1 b a res i j);
    let h2 = ST.get () in
    let q i1 = forall (j:size_nat{j < v n2}) (k:size_nat{k < 8}).
      get h2 res i1 (8 * j + k) == S.frodo_key_encode_inner (v b) (B.as_seq h0 a) i1 j k in
    onemore (fun i1 -> i1 < v params_nbar) q (v i)
  );
  let h1 = ST.get () in
  S.lemma_matrix_equality_nbar (as_matrix h1 res) (S.frodo_key_encode (v b) (B.as_seq h0 a));
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
