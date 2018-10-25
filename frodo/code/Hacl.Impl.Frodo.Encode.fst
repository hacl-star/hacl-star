module Hacl.Impl.Frodo.Encode

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Matrix
open Hacl.Impl.Frodo.Params

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST

module LSeq = Lib.Sequence
module S    = Spec.Frodo.Encode
module Lemmas = Spec.Frodo.Lemmas

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

inline_for_extraction noextract private
val ec:
    b:size_t{0 < v b /\ v b < v params_logq}
  -> k:uint16{uint_v k < pow2 (v b)}
  -> r:uint16{r == S.ec (v b) k}
let ec b a =
  a <<. (params_logq -. b)

inline_for_extraction noextract private
val dc:
    b:size_t{0 < v b /\ v b < v params_logq}
  -> c:uint16
  -> r:uint16{r == S.dc (v b) c}
let dc b c =
  let res1 = (c +. (u16 1 <<. (params_logq -. b -. size 1))) >>. (params_logq -. b) in
  res1 &. ((u16 1 <<. b) -. u16 1)

inline_for_extraction noextract private
val ec1:
    b:size_t{0 < v b /\ v b <= 8}
  -> x:uint64
  -> k:size_t{v k < 8}
  -> res:uint16{res == S.ec1 (v b) x (v k)}
let ec1 b x k =
  Lemmas.modulo_pow2_u64 (x >>. (b *! k)) (v b);
  let rk = (x >>. (b *! k)) &. ((u64 1 <<. b) -. u64 1) in
  ec b (to_u16 rk)

inline_for_extraction noextract private
val frodo_key_encode1:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> i:size_t{v i < v params_nbar}
  -> Stack uint64
    (requires fun h -> B.live h a)
    (ensures fun h0 r h1 ->
      modifies loc_none h0 h1 /\
      r == S.frodo_key_encode1 (v b) (as_seq h0 a) (v i))
let frodo_key_encode1 b a i =
  push_frame();
  let v8 = create (size 8) (u8 0) in
  update_sub v8 (size 0) b (sub #_ #_ #(v b) a (i *! b) b);
  let x = uint_from_bytes_le #U64 v8 in
  pop_frame();
  x

inline_for_extraction noextract private
val frodo_key_encode2:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> i:size_t{v i < v params_nbar}
  -> x:uint64
  -> res:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      B.live h a /\ B.live h res /\ B.disjoint a res)
    (ensures fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res ==
      Lib.LoopCombinators.repeati 8 (S.frodo_key_encode0 (v b) (as_seq h0 a) x (v i)) (as_matrix h0 res))
let frodo_key_encode2 b a i x res =
  [@ inline_let]
  let spec h0 = S.frodo_key_encode0 (v b) (as_seq h0 a) x (v i) in
  let h0 = ST.get () in
  loop1 h0 (size 8) res spec
  (fun k ->
    Lib.LoopCombinators.unfold_repeati 8 (spec h0) (as_seq h0 res) (v k);
    mset res i k (ec1 b x k)
  )

val frodo_key_encode:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> res:matrix_t params_nbar params_nbar
  -> Stack unit
    (requires fun h ->
      B.live h a /\ B.live h res /\ B.disjoint a res)
    (ensures fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_matrix h1 res == S.frodo_key_encode (v b) (as_seq h0 a))
[@"c_inline"]
let frodo_key_encode b a res =
  (* TODO: we don't need to call the memset function
     since we know that the frodo_key_encode function
     doesn't depend on the initial values of the res buffer *)
  memset res (u16 0) (params_nbar *! params_nbar);
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v params_nbar * v params_nbar)) (as_seq h0 res);
  [@ inline_let]
  let spec h0 = S.frodo_key_encode2 (v b) (as_seq h0 a) in
  loop1 h0 params_nbar res spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v params_nbar) (spec h0) (as_seq h0 res) (v i);
    let x = frodo_key_encode1 b a i in
    frodo_key_encode2 b a i x res
  )

inline_for_extraction noextract private
val frodo_key_decode1:
    b:size_t{0 < v b /\ v b <= 8}
  -> i:size_t{v i < v params_nbar}
  -> templong:uint64
  -> res:lbytes (params_nbar *! params_nbar *! b /. size 8)
  -> Stack unit
    (requires fun h -> B.live h res)
    (ensures fun h0 _ h1 ->
      modifies (loc_buffer res) h0 h1 /\
      as_seq h1 res == S.frodo_key_decode1 (v b) (v i) templong (as_seq h0 res))
let frodo_key_decode1 b i templong res =
  push_frame();
  let v8 = create #uint8 #8 (size 8) (u8 0) in
  uint_to_bytes_le #_ #SEC v8 templong;
  let tmp = sub #uint8 #8 #(v b) v8 (size 0) b in
  update_sub res (i *! b) b tmp;
  pop_frame()

inline_for_extraction noextract private
val frodo_key_decode2:
    b:size_t{0 < v b /\ v b <= 8}
  -> a:matrix_t params_nbar params_nbar
  -> i:size_t{v i < v params_nbar}
  -> Stack uint64
    (requires fun h -> B.live h a)
    (ensures fun h0 r h1 ->
      modifies loc_none h0 h1 /\
      r == Lib.LoopCombinators.repeat_gen 8 S.decode_templong_t
           (S.frodo_key_decode0 (v b) (as_matrix h0 a) (v i)) (u64 0))
let frodo_key_decode2 b a i =
  push_frame();
  let templong = create #uint64 #1 (size 1) (u64 0) in
  [@ inline_let]
  let refl h i : GTot uint64 = B.get h templong 0 in
  [@ inline_let]
  let footprint i = loc_buffer templong in
  [@ inline_let]
  let spec h0 = S.frodo_key_decode0 (v b) (as_matrix h0 a) (v i) in
  let h0 = ST.get () in
  assert (bget h0 templong 0 == u64 0);
  loop h0 (size 8) S.decode_templong_t refl footprint spec
  (fun k ->
    Lib.LoopCombinators.unfold_repeat_gen 8 S.decode_templong_t (spec h0) (refl h0 0) (v k);
    let aik = mget a i k in
    templong.(size 0) <- templong.(size 0) |. (to_u64 (dc b aik) <<. (b *! k))
  );
  let templong = templong.(size 0) in
  pop_frame();
  templong

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
  (* TODO: we don't need to call the memset function
     since we know that the frodo_key_decode function
     doesn't depend on the initial values of the res buffer *)
  memset res (u8 0) resLen;
  let h0 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h0 res) 0 (v resLen)) (as_seq h0 res);
  [@ inline_let]
  let spec h0 = S.frodo_key_decode2 (v b) (as_seq h0 a) in
  loop1 h0 params_nbar res spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v params_nbar) (spec h0) (as_seq h0 res) (v i);
    let templong = frodo_key_decode2 b a i in
    frodo_key_decode1 b i templong res
  )
