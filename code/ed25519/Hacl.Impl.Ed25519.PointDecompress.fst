module Hacl.Impl.Ed25519.PointDecompress

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51

module SC = Spec.Curve25519
module SE = Spec.Ed25519

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val most_significant_bit:
  s:lbuffer uint8 32ul ->
  Stack uint64
    (requires fun h -> live h s)
    (ensures fun h0 z h1 -> h0 == h1 /\
      (v z = 0 \/ v z = 1) /\
      v z == (nat_from_bytes_le (as_seq h0 s) / pow2 255) % 2
    )

open FStar.Calc

let most_significant_bit s =
  let s31 = s.(31ul) in
  let z   = s31 >>. 7ul in
  (**) let h0 = get() in
  (**) FStar.Math.Lemmas.lemma_div_lt_nat (v s31) 8 7;
  (**) uints_from_bytes_le_nat_lemma #U8 #SEC #32 (as_seq h0 s);
  (**) nat_from_intseq_le_slice_lemma (as_seq h0 s) 31;
  (**) nat_from_intseq_le_lemma0 (Seq.slice (as_seq h0 s) 31 32);
  (**) assert_norm (31 * 8 == 248);
  (**) FStar.Math.Lemmas.lemma_div_mod_plus (nat_from_intseq_le (Seq.slice (as_seq h0 s) 0 31))
    (v s31) (pow2 248);
  (**) FStar.Math.Lemmas.small_div (nat_from_intseq_le (Seq.slice (as_seq h0 s) 0 31)) (pow2 248);
  (**) FStar.Math.Lemmas.division_multiplication_lemma (nat_from_bytes_le (as_seq h0 s)) (pow2 248) (pow2 7);
  (**) assert_norm (pow2 248 * pow2 7 = pow2 255);
  (**) FStar.Math.Lemmas.small_mod (v s31 / pow2 7) 2;
  to_u64 z

inline_for_extraction noextract
val point_decompress_:
    out:point
  -> s:lbuffer uint8 32ul
  -> tmp:lbuffer uint64 10ul ->
  Stack bool
    (requires fun h ->
      live h out /\ live h s /\ live h tmp /\
      disjoint s tmp /\ disjoint out tmp /\
      F51.point_inv_t h out /\
      F51.mul_inv_t h (gsub tmp 5ul 5ul)
    )
    (ensures  fun h0 b h1 -> modifies (loc out |+| loc tmp) h0 h1 /\
      (b <==> Some? (SE.point_decompress (as_seq h0 s))) /\
      (b ==> F51.point_inv_t h1 out) /\
      (b ==> (F51.point_eval h1 out == Some?.v (SE.point_decompress (as_seq h0 s))))
    )

#push-options "--z3rlimit 30"

let point_decompress_ out s tmp =
  let y    = sub tmp 0ul 5ul in
  let x    = sub tmp 5ul 5ul in
  let h0 = get() in
  let sign = most_significant_bit s in
  let h1 = get() in
  load_51 y s;
  let h2 = get() in
  let z = Hacl.Impl.Ed25519.RecoverX.recover_x x y sign in

  let res =
  if z = false then false
  else (
    let outx = getx out in
    let outy = gety out in
    let outz = getz out in
    let outt = gett out in
    copy outx x;
    copy outy y;
    make_one outz;
    fmul outt x y;
    let h1 = get() in
    true
  ) in
  res

val point_decompress:
    out:point
  -> s:lbuffer uint8 32ul ->
  Stack bool
    (requires fun h -> live h out /\ live h s /\ F51.point_inv_t h out)
    (ensures  fun h0 b h1 -> modifies (loc out) h0 h1 /\
      (b ==> F51.point_inv_t h1 out) /\
      (b <==> Some? (Spec.Ed25519.point_decompress (as_seq h0 s))) /\
      (b ==> (F51.point_eval h1 out == Some?.v (Spec.Ed25519.point_decompress (as_seq h0 s))))
    )
let point_decompress out s =
  push_frame();
  let tmp  = create 10ul (u64 0) in
  let res = point_decompress_ out s tmp in
  pop_frame();
  res

#pop-options
