module Hacl.Impl.Frodo.Encode

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
    b:size_t{0 < v b /\ v b < v params_logq}
  -> k:uint16{uint_v k < pow2 (v b)}
  -> r:uint16{r == S.ec (v b) k}
let ec b a =
  a <<. (size_to_uint32 (params_logq -. b))

inline_for_extraction noextract private
val dc:
    b:size_t{0 < v b /\ v b < v params_logq}
  -> c:uint16
  -> r:uint16{r == S.dc (v b) c}
let dc b c =
  let res1 = (c +. (u16 1 <<. size_to_uint32 (params_logq -. b -. size 1))) >>. size_to_uint32 (params_logq -. b) in
  res1 &. ((u16 1 <<. size_to_uint32 b) -. u16 1)

inline_for_extraction noextract private
val ec1:
    b:size_t{0 < v b /\ v b <= 8}
  -> x:uint64
  -> k:size_t{v k < 8}
  -> res:uint16{res == S.ec1 (v b) x (v k)}
let ec1 b x k =
  FLemmas.modulo_pow2_u64 (x >>. size_to_uint32 (b *! k)) (v b);
  let rk = (x >>. size_to_uint32 (b *! k)) &. ((u64 1 <<. size_to_uint32 b) -. u64 1) in
  ec b (to_u16 rk)

inline_for_extraction noextract private
val frodo_key_encode1:
    b:size_t{0 < v b /\ v b <= 8}
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
    b:size_t{0 < v b /\ v b <= 8}
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

#set-options "--max_fuel 1"

val frodo_key_encode:
    b:size_t{0 < v b /\ v b <= 8}
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
      get h1 res i0 k == S.frodo_key_encode_fc (v b) (B.as_seq h0 a) i0 k) /\
    (forall (i0:size_nat{i <= i0 /\ i0 < v params_nbar}) (k:size_nat{k < 8}).
      get h1 res i0 k == get h0 res i0 k))
  (fun i ->
    frodo_key_encode2 b a res i
  );
  let h1 = ST.get () in
  S.lemma_matrix_equality_nbar (as_matrix h1 res) (S.frodo_key_encode (v b) (B.as_seq h0 a));
  pop_frame()

inline_for_extraction noextract private
val frodo_key_decode1:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:matrix_t params_nbar params_nbar
  -> i:size_t{v i < v params_nbar}
  -> Stack uint64
    (requires fun h -> B.live h a)
    (ensures fun h0 r h1 ->
      B.live h1 a /\ modifies loc_none h0 h1 /\
      r == S.frodo_key_decode1 (v b) (as_matrix h0 a) (v i))
let frodo_key_decode1 b a i =
  push_frame();
  let h0 = ST.get () in
  let templong = create #uint64 #1 (size 1) (u64 0) in
  let h1 = ST.get () in
  Lib.Loops.for (size 0) (size 8)
    (fun h2 k -> B.live h1 templong /\ B.live h2 templong /\
      modifies (loc_buffer templong) h1 h2 /\
      bget h2 templong 0 == S.decode_fc (v b) (as_matrix h0 a) (v i) k)
    (fun k ->
      let aik = mget a i k in
      templong.(size 0) <- templong.(size 0) |. (to_u64 (dc b aik) <<. size_to_uint32 (b *! k))
    );
  let res = templong.(size 0) in
  pop_frame();
  res

#set-options "--max_fuel 0"

inline_for_extraction noextract private
val frodo_key_decode2:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:matrix_t params_nbar params_nbar
  -> i:size_t{v i < v params_nbar}
  -> res:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h res /\ B.disjoint a res)
    (ensures fun h0 _ h1 ->
      B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
      B.as_seq h1 res == S.frodo_key_decode2 (v b) (as_matrix h0 a) (v i) (B.as_seq h0 res))
let frodo_key_decode2 b a i res =
  push_frame();
  let templong = frodo_key_decode1 b a i in
  let v8 = create (size 8) (u8 0) in
  uint_to_bytes_le #U64 v8 templong;
  let tmp = sub #uint8 #8 #(v b) v8 (size 0) b in
  update_sub res (i *! b) b tmp;
  pop_frame()

val lemma_eq_intro_decode:
    b:size_nat{0 < b /\ b <= 8}
  -> s1:LSeq.lseq uint8 (v params_nbar * v params_nbar * b / 8)
  -> s2:LSeq.lseq uint8 (v params_nbar * v params_nbar * b / 8)
  -> Lemma
    (requires forall (i:size_nat{i < v params_nbar}) (k:size_nat{k < b}). LSeq.index s1 (i * b + k) == LSeq.index s2 (i * b + k))
    (ensures  s1 == s2)
let lemma_eq_intro_decode b s1 s2 =
  let resLen = v params_nbar * b in
  assert (forall (i:size_nat{i < v params_nbar}) (k:size_nat{k < b}).
    LSeq.index s1 (i * b + k) == LSeq.index s2 (i * b + k));
  assert (forall (l:size_nat{l < resLen}). l == (l / b) * b + l % b /\ l / b < v params_nbar /\ l % b < b);
  assert (forall (l:size_nat{l < resLen}). LSeq.index s1 l == LSeq.index s2 l);
  LSeq.eq_intro s1 s2

val frodo_key_decode:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:matrix_t params_nbar params_nbar
  -> res:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> Stack unit
    (requires fun h -> B.live h a /\ B.live h res /\ B.disjoint a res)
    (ensures  fun h0 _ h1 ->
      B.live h1 res /\ modifies (loc_buffer res) h0 h1 /\
      B.as_seq h1 res == S.frodo_key_decode (v b) (as_matrix h0 a))
[@"c_inline"]
let frodo_key_decode b a res =
  let resLen = params_nbar *! params_nbar *! b /. size 8 in
  let h0 = ST.get () in
  Lib.Loops.for (size 0) params_nbar
    (fun h1 i ->
      B.live h0 a /\ B.live h1 a /\ B.live h0 res /\ B.live h1 res /\
      modifies (loc_buffer res) h0 h1 /\
      (forall (i0:size_nat{i0 < i}) (k:size_nat{k < v b}).
	 bget h1 res (i0 * v b + k) == S.frodo_key_decode_fc (v b) (B.as_seq h0 a) i0 k))
    (fun i ->
      frodo_key_decode2 b a i res
    );
  let h1 = ST.get () in
  lemma_eq_intro_decode (v b) (B.as_seq h1 res) (S.frodo_key_decode (v b) (as_matrix h0 a))
