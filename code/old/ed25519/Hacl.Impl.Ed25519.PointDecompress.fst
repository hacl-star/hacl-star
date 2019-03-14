module Hacl.Impl.Ed25519.PointDecompress

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open FStar.UInt64
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


#reset-options "--max_fuel 0 --z3rlimit 100"

open FStar.Mul

private
val lemma_most_significant_bit:
  s:Seq.seq UInt8.t{Seq.length s = 32} ->
  Lemma (UInt8.v (Seq.index s 31) = FStar.Old.Endianness.little_endian s / pow2 248)
let lemma_most_significant_bit s =
  let open FStar.Seq in
  let s31 = index s 31 in
  lemma_eq_intro s (slice s 0 31 @| slice s 31 32);
  lemma_eq_intro (slice s 31 32) (create 1 s31);
  FStar.Old.Endianness.little_endian_append (slice s 0 31) (slice s 31 32);
  FStar.Old.Endianness.little_endian_singleton s31;
  Math.Lemmas.lemma_div_mod (FStar.Old.Endianness.little_endian s) (pow2 248);
  assert(FStar.Old.Endianness.little_endian s ==
    FStar.Old.Endianness.little_endian (slice s 0 31) + pow2 248 * FStar.Old.Endianness.little_endian (slice s 31 32));
  FStar.Old.Endianness.lemma_little_endian_is_bounded (slice s 0 31);
  Math.Lemmas.division_addition_lemma (FStar.Old.Endianness.little_endian (slice s 0 31)) (pow2 248) (UInt8.v s31);
  Math.Lemmas.small_division_lemma_1 (FStar.Old.Endianness.little_endian (slice s 0 31)) (pow2 248)


inline_for_extraction
private
val most_significant_bit:
  s:buffer UInt8.t{length s = 32} ->
  Stack UInt64.t
    (requires (fun h -> live h s))
    (ensures (fun h0 z h1 -> live h0 s /\ h1 == h0 /\
      v z == (FStar.Old.Endianness.little_endian (as_seq h0 s) / pow2 255) % 2))
let most_significant_bit s =
  let h = ST.get() in
  let s31 = s.(31ul) in
  lemma_most_significant_bit (as_seq h s);
  assert(UInt8.v s31 = FStar.Old.Endianness.little_endian (as_seq h s) / pow2 248);
  let z   = FStar.UInt8.(s31 >>^ 7ul) in
  Math.Lemmas.division_multiplication_lemma (FStar.Old.Endianness.little_endian (as_seq h s)) (pow2 248) (pow2 7);
  Math.Lemmas.pow2_plus 248 7;
  assert(UInt8.v z = (FStar.Old.Endianness.little_endian (as_seq h s) / pow2 255));
  FStar.Old.Endianness.lemma_little_endian_is_bounded (as_seq h s);
  Math.Lemmas.lemma_div_lt (FStar.Old.Endianness.little_endian (as_seq h s)) 256 255;
  assert_norm(pow2 1 = 2);
  Math.Lemmas.modulo_lemma (UInt8.v z) 2;
  Int.Cast.uint8_to_uint64 z


inline_for_extraction
private
val copy:
  a:buffer Hacl.UInt64.t{length a = 5} ->
  b:buffer Hacl.UInt64.t{length b = 5 /\ disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h0 a == as_seq h1 b))
let copy a b =
  let h = ST.get() in
  blit a 0ul b 0ul 5ul;
  let h' = ST.get() in
  Seq.lemma_eq_intro (as_seq h a) (Seq.slice (as_seq h a) 0 5);
  Seq.lemma_eq_intro (as_seq h' b) (Seq.slice (as_seq h' b) 0 5)


inline_for_extraction
private
val make_one:
  b:buffer Hacl.UInt64.t{length b = 5} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1 /\ seval (as_seq h1 b) == 1
      /\ Hacl.Bignum25519.red_513 (as_seq h1 b)))
let make_one b =
  let zero = Hacl.Cast.uint64_to_sint64 0uL in
  let one  = Hacl.Cast.uint64_to_sint64 1uL in
  Hacl.Lib.Create64.make_h64_5 b one zero zero zero zero;
  let h = ST.get() in
  lemma_reveal_seval (as_seq h b);
  assert_norm(pow2 51 = 0x8000000000000);
  lemma_intro_red_51 (as_seq h b);
  lemma_red_51_is_red_513 (as_seq h b)


#reset-options "--max_fuel 0 --z3rlimit 100"


private
let lemma_modifies_2 #a #a' h (b:buffer a{live h b}) (b':buffer a'{live h b'}) :
  Lemma (modifies_2 b b' h h)
  = lemma_intro_modifies_2 b b' h h


private
let lemma_modifies_1 #a h (b:buffer a{live h b}) :
  Lemma (modifies_1 b h h)
  = lemma_intro_modifies_1 b h h


inline_for_extraction
private
val point_decompress_step_1:
  s:buffer UInt8.t{length s = 32} ->
  tmp:buffer UInt64.t{length tmp = 10 /\ disjoint s tmp} ->
  Stack bool
    (requires (fun h -> live h s /\ live h tmp))
    (ensures (fun h0 b h1 -> live h0 s /\ modifies_1 tmp h0 h1 /\ live h1 tmp /\
      (let y' = as_seq h1 (Buffer.sub tmp 0ul 5ul) in
       let x' = as_seq h1 (Buffer.sub tmp 5ul 5ul) in
       let y = FStar.Old.Endianness.little_endian (as_seq h0 s) in
       let sign = (y / pow2 255) % 2 = 1 in
       let y = y % pow2 255 in
       let x = Spec.Ed25519.recover_x y sign in
       if b then (Some? x /\ seval x' == Some?.v x /\ seval y' == y % Spec.Curve25519.prime /\
                  red_513 x' /\ red_513 y' /\ b == true)
       else (None? x))
    ))
#reset-options "--max_fuel 0 --z3rlimit 500"
let point_decompress_step_1 s tmp =
  let h0 = ST.get() in
  let y    = Buffer.sub tmp 0ul 5ul in
  let x    = Buffer.sub tmp 5ul 5ul in
  let sign = most_significant_bit s in
  Hacl.Impl.Load51.load_51 y s;
  let h = ST.get() in
  lemma_reveal_seval (as_seq h y);
  let z = Hacl.Impl.Ed25519.RecoverX.recover_x x y sign in
  let h = ST.get() in
  if z then (
    lemma_red_51_is_red_513 (as_seq h x);
    lemma_red_51_is_red_513 (as_seq h y));
  let h1 = ST.get() in
  z


inline_for_extraction
private
val point_decompress_:
  out:point ->
  s:buffer Hacl.UInt8.t{length s = 32} ->
  tmp:buffer Hacl.UInt64.t{length tmp = 10 /\ disjoint s tmp /\ disjoint out tmp} ->
  Stack bool
    (requires (fun h -> live h out /\ live h s /\ live h tmp))
    (ensures (fun h0 b h1 -> live h0 s /\ live h1 out /\ modifies_2 out tmp h0 h1 /\
      (let px = as_seq h1 (getx out) in let py = as_seq h1 (gety out) in
       let pz = as_seq h1 (getz out) in let pt = as_seq h1 (gett out) in
       (if b then (
         Some? (Spec.Ed25519.point_decompress (as_seq h0 s)) /\
         (seval px, seval py, seval pz, seval pt) == Some?.v (Spec.Ed25519.point_decompress (as_seq h0 s)) /\
         red_513 px /\ red_513 py /\ red_513 pz /\ red_513 pt)
       else None? (Spec.Ed25519.point_decompress (as_seq h0 s)) ))
    ))
#reset-options "--max_fuel 0 --z3rlimit 200"
let point_decompress_ out s tmp =
  let y    = Buffer.sub tmp 0ul 5ul in
  let x    = Buffer.sub tmp 5ul 5ul in
  let z = point_decompress_step_1 s tmp in
  let h = ST.get() in
  lemma_reveal_seval (as_seq h y);
  let res =
  if z = false then (
    let h = ST.get() in
    lemma_modifies_1 h out;
    false
  ) else (
    let outx = getx out in
    let outy = gety out in
    let outz = getz out in
    let outt = gett out in
    let h = ST.get() in
    lemma_red_513_is_red_53 (as_seq h x);
    lemma_red_513_is_red_5413 (as_seq h y);
    copy x outx;
    copy y outy;
    make_one outz;
    fmul outt x y;
    true
  ) in
  res

#reset-options "--max_fuel 0 --z3rlimit 100"
let point_decompress out s =
  let h0 = ST.get() in
  push_frame();
  let tmp  = Buffer.create 0uL 10ul in
  let res = point_decompress_ out s tmp in
  pop_frame();
  res
