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
  -> x:uint64
  -> k:size_t{v k < 8}
  -> res:uint16{res == S.ec1 (v b) x (v k)}
let ec1 b x k =
  FLemmas.modulo_pow2_u64 (x >>. size_to_uint32 (b *! k)) (v b);
  let rk = (x >>. size_to_uint32 (b *! k)) &. ((u64 1 <<. size_to_uint32 b) -. u64 1) in
  ec b (to_u16 rk)

inline_for_extraction noextract private
val frodo_key_encode1:
    b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res0:matrix_t params_nbar params_nbar
  -> vi:uint64
  -> i:size_t{v i < v params_nbar}
  -> Stack unit
    (requires fun h ->
      B.live h a /\ B.live h res0 /\ B.disjoint a res0)
    (ensures fun h0 _ h1 ->
      B.live h1 res0 /\ modifies (loc_buffer res0) h0 h1 /\
      as_matrix h1 res0 == S.frodo_key_encode1 (v b) (B.as_seq h0 a) (as_matrix h0 res0) vi (v i))
let frodo_key_encode1 b a res0 vi i =
  let h0 = ST.get () in
  Lib.Loops.for (size 0) (size 8)
  (fun h1 k ->
    B.live h1 res0 /\ B.live h1 a /\ modifies (loc_buffer res0) h0 h1 /\
    (forall (i0:size_nat{i0 < v params_nbar /\ i0 <> v i}) (k:size_nat{k < 8}).
      get h1 res0 i0 k == get h0 res0 i0 k) /\
    (forall (k1:size_nat{k1 < k}). get h1 res0 (v i) k1 == S.ec1 (v b) vi k1) /\
    (forall (k1:size_nat{k <= k1 /\ k1 < 8}). get h1 res0 (v i) k1 == get h0 res0 (v i) k1))
  (fun k ->
    mset res0 i k (ec1 b vi k)
  );
  let h2 = ST.get () in
  S.lemma_matrix_equality_nbar (as_matrix h2 res0) (S.frodo_key_encode1 (v b) (B.as_seq h0 a) (as_matrix h0 res0) vi (v i))

inline_for_extraction noextract private
val frodo_key_encode2:
    b:size_t{v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res0:matrix_t params_nbar params_nbar
  -> i:size_t{v i < v params_nbar}
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h res0 /\ B.disjoint a res0)
    (ensures  fun h0 _ h1 ->
      B.live h1 a /\ B.live h1 res0 /\
      modifies (loc_buffer res0) h0 h1 /\
      as_matrix h1 res0 == S.frodo_key_encode2 (v b) (B.as_seq h0 a) (as_matrix h0 res0) (v i))
let frodo_key_encode2 b a res0 i =
  push_frame();
  let v8 = create (size 8) (u8 0) in
  let aLen = params_nbar *! params_nbar *! b /. size 8 in
  update_sub v8 (size 0) b (sub #_ #_ #(v b) a (i *! b) b);
  let vi = uint_from_bytes_le #U64 v8 in
  frodo_key_encode1 b a res0 vi i;
  pop_frame()

#set-options "--z3rlimit 50"

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

  let h0 = ST.get () in
  Lib.Loops.for (size 0) params_nbar
  (fun h1 i ->
    B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
    (forall (i0:size_nat{i0 < i}) (k:size_nat{k < 8}).
      get h1 res i0 k == S.frodo_key_encode_inner (v b) (B.as_seq h0 a) i0 k) /\
    (forall (i0:size_nat{i <= i0 /\ i0 < v params_nbar}) (k:size_nat{k < 8}).
      get h1 res i0 k == get h0 res i0 k))
  (fun i ->
    frodo_key_encode2 b a res i
  );
  let h1 = ST.get () in
  S.lemma_matrix_equality_nbar (as_matrix h1 res) (S.frodo_key_encode (v b) (B.as_seq h0 a));
  pop_frame()


val frodo_key_decode:
    b:size_t{v b <= 8}
  -> a:matrix_t params_nbar params_nbar
  -> res:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h res /\ B.disjoint a res)
    (ensures  fun h0 r h1 -> B.live h1 res /\ modifies (loc_buffer res) h0 h1)
[@"c_inline"]
let frodo_key_decode b a res =
  push_frame();
  let resLen = params_nbar *! params_nbar *! b /. size 8 in

  let v8 = create (size 8) (u8 0) in
  let templong:lbuffer uint64 1 = create (size 1) (u64 0) in

  let h0 = ST.get () in
  let inv (h1:mem) (j:nat{j <= v params_nbar}) =
    B.live h1 res /\ B.live h1 v8 /\ B.live h1 templong /\
    modifies (loc_union (loc_buffer res) (loc_union (loc_buffer v8) (loc_buffer templong))) h0 h1 in
  let f' (i:size_t{0 <= v i /\ v i < v params_nbar}): Stack unit
    (requires (fun h -> inv h (v i)))
    (ensures (fun _ _ h2 -> inv h2 (v i + 1))) =
      templong.(size 0) <- u64 0;
      let h1 = ST.get () in
      loop_nospec #h1 (size 8) templong
      (fun k ->
        let aijk = mget a i k in
        let aij = dc b aijk in
        templong.(size 0) <- templong.(size 0) |. (to_u64 aij <<. size_to_uint32 (b *! k))
      );
      uint_to_bytes_le #U64 v8 (templong.(size 0));
      copy (sub res (i *! b) b) b (sub #uint8 #8 #(v b) v8 (size 0) b) in

  Lib.Loops.for (size 0) params_nbar inv f';
  pop_frame()
