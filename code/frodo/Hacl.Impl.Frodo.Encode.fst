module Hacl.Impl.Frodo.Encode

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Matrix

module ST = FStar.HyperStack.ST
module Loops = Lib.LoopCombinators
module LSeq = Lib.Sequence
module S    = Spec.Frodo.Encode

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract private
val ec:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= v logq}
  -> k:uint16{v k < pow2 (v b)}
  -> r:uint16{r == S.ec (v logq) (v b) k}

let ec logq b a =
  a <<. (logq -. b)


inline_for_extraction noextract private
val dc:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b < v logq}
  -> c:uint16
  -> r:uint16{r == S.dc (v logq) (v b) c}

let dc logq b c =
  let res1 = (c +. (u16 1 <<. (logq -. b -. size 1))) >>. (logq -. b) in
  res1 &. ((u16 1 <<. b) -. u16 1)


inline_for_extraction noextract private
val ec1:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b <= v logq}
  -> x:uint64
  -> k:size_t{v k < 8}
  -> res:uint16{res == S.ec1 (v logq) (v b) x (v k)}

let ec1 logq b x k =
  Spec.Frodo.Lemmas.modulo_pow2_u64 (x >>. (b *! k)) (v b);
  let rk = (x >>. (b *! k)) &. ((u64 1 <<. b) -. u64 1) in
  ec logq b (to_u16 rk)


inline_for_extraction noextract private
val frodo_key_encode1:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b <= v logq}
  -> n:size_t{v n == 8}
  -> a:lbytes (n *! n *! b /. size 8)
  -> i:size_t{v i < v n}
  -> Stack uint64
    (requires fun h -> live h a)
    (ensures fun h0 r h1 -> modifies0 h0 h1 /\
      r == S.frodo_key_encode1 (v logq) (v b) (v n) (as_seq h0 a) (v i))

let frodo_key_encode1 logq b n a i =
  let h0 = ST.get() in
  push_frame();
  let v8 = create (size 8) (u8 0) in
  let chunk = sub a (i *! b) b in
  let h1 = ST.get() in
  assert (as_seq h1 chunk == LSeq.sub (as_seq h0 a) (v (i *! b)) (v b));
  update_sub v8 (size 0) b chunk;
  let x = uint_from_bytes_le #U64 v8 in
  pop_frame();
  x


inline_for_extraction noextract private
val frodo_key_encode2:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b <= v logq}
  -> n:size_t{v n == 8}
  -> a:lbytes (n *! n *! b /. size 8)
  -> i:size_t{v i < v n}
  -> x:uint64
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ disjoint a res)
    (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res ==
      Loops.repeati 8 (S.frodo_key_encode0 (v logq) (v b) (v n) (as_seq h0 a) x (v i)) (as_matrix h0 res))

let frodo_key_encode2 logq b n a i x res =
  [@ inline_let]
  let spec h0 = S.frodo_key_encode0 (v logq) (v b) (v n) (as_seq h0 a) x (v i) in
  let h0 = ST.get () in
  loop1 h0 (size 8) res spec
  (fun k ->
    Loops.unfold_repeati 8 (spec h0) (as_seq h0 res) (v k);
    mset res i k (ec1 logq b x k)
  )


val frodo_key_encode:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b <= v logq}
  -> n:size_t{v n == 8}
  -> a:lbytes (n *! n *! b /. size 8)
  -> res:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ disjoint a res /\
      as_seq h res == Spec.Matrix.create (v n) (v n))
    (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_matrix h1 res == S.frodo_key_encode (v logq) (v b) (v n) (as_seq h0 a))

[@"c_inline"]
let frodo_key_encode logq b n a res =
  let h0 = ST.get () in
  [@ inline_let]
  let spec h0 = S.frodo_key_encode2 (v logq) (v b) (v n) (as_seq h0 a) in
  loop1 h0 n res spec
  (fun i ->
    Loops.unfold_repeati (v n) (spec h0) (as_seq h0 res) (v i);
    let x = frodo_key_encode1 logq b n a i in
    frodo_key_encode2 logq b n a i x res
  )


inline_for_extraction noextract private
val frodo_key_decode1:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b < v logq}
  -> n:size_t{v n == 8}
  -> i:size_t{v i < v n}
  -> templong:uint64
  -> res:lbytes (n *! n *! b /. size 8)
  -> Stack unit
    (requires fun h -> live h res)
    (ensures fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_seq h1 res == S.frodo_key_decode1 (v logq) (v b) (v n) (v i) templong (as_seq h0 res))

let frodo_key_decode1 logq b n i templong res =
  push_frame();
  let v8 = create (size 8) (u8 0) in
  uint_to_bytes_le v8 templong;
  let tmp = sub v8 (size 0) b in
  update_sub res (i *! b) b tmp;
  pop_frame()


inline_for_extraction noextract private
val frodo_key_decode2:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b < v logq}
  -> n:size_t{v n == 8}
  -> a:matrix_t n n
  -> i:size_t{v i < v n}
  -> Stack uint64
    (requires fun h -> live h a)
    (ensures fun h0 r h1 -> modifies0 h0 h1 /\
      r == Loops.repeat_gen 8 S.decode_templong_t
        (S.frodo_key_decode0 (v logq) (v b) (v n) (as_matrix h0 a) (v i)) (u64 0))

let frodo_key_decode2 logq b n a i =
  push_frame();
  let templong = create (size 1) (u64 0) in
  [@ inline_let]
  let refl h i : GTot uint64 = bget h templong 0 in
  [@ inline_let]
  let footprint i = loc templong in
  [@ inline_let]
  let spec h0 = S.frodo_key_decode0 (v logq) (v b) (v n) (as_matrix h0 a) (v i) in
  let h0 = ST.get () in
  assert (bget h0 templong 0 == u64 0);
  loop h0 (size 8) S.decode_templong_t refl footprint spec
  (fun k ->
    Loops.unfold_repeat_gen 8 S.decode_templong_t (spec h0) (refl h0 0) (v k);
    let aik = mget a i k in
    templong.(size 0) <- templong.(size 0) |. (to_u64 (dc logq b aik) <<. (b *! k))
  );
  let templong = templong.(size 0) in
  pop_frame();
  templong


val frodo_key_decode:
    logq:size_t{0 < v logq /\ v logq <= 16}
  -> b:size_t{0 < v b /\ v b <= 8 /\ v b < v logq}
  -> n:size_t{v n == 8}
  -> a:matrix_t n n
  -> res:lbytes (n *! n *! b /. size 8)
  -> Stack unit
    (requires fun h ->
      live h a /\ live h res /\ disjoint a res /\
      as_seq h res == LSeq.create (v n * v n * v b / 8) (u8 0))
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      as_seq h1 res == S.frodo_key_decode (v logq) (v b) (v n) (as_matrix h0 a))

[@"c_inline"]
let frodo_key_decode logq b n a res =
  [@ inline_let]
  let spec h0 = S.frodo_key_decode2 (v logq) (v b) (v n) (as_seq h0 a) in
  let h0 = ST.get() in
  loop1 h0 n res spec
  (fun i ->
    Loops.unfold_repeati (v n) (spec h0) (as_seq h0 res) (v i);
    let templong = frodo_key_decode2 logq b n a i in
    frodo_key_decode1 logq b n i templong res
  )
