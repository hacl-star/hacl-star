module Hacl.Impl.Ed25519.PointCompress

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Buffer
open Hacl.UInt64
open Hacl.Bignum25519


#reset-options "--max_fuel 0 --z3rlimit 100"

let hint8_p = buffer Hacl.UInt8.t
let hint64_p = buffer Hacl.UInt64.t

let op_String_Access (h:HyperStack.mem) (b:hint8_p{live h b}) =
  Hacl.Spec.Endianness.reveal_sbytes (as_seq h b)

open FStar.Mul

private let lemma_distr_4 a b c d e : Lemma (a * (b + c + d + e) == a * b + a * c + a * d + a * e)
  = Math.Lemmas.distributivity_add_right a (b + c + d) e;
    Math.Lemmas.distributivity_add_right a (b + c) d;
    Math.Lemmas.distributivity_add_right a (b) c


private let lemma_x_mod_2 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) :
  Lemma ((a + pow2 51 * b + pow2 102 * c + pow2 153 * d + pow2 204 * e) % 2 = a % 2)
  = assert_norm(pow2 51 = 2 * pow2 50);
    assert_norm(pow2 102 = 2 * pow2 101);
    assert_norm(pow2 153 = 2 * pow2 152);
    assert_norm(pow2 204 = 2 * pow2 203);
    lemma_distr_4 2 (pow2 50 * b) (pow2 101 * c) (pow2 152 * d) (pow2 203 * e);
    Math.Lemmas.paren_mul_right 2 (pow2 50) b;
    Math.Lemmas.paren_mul_right 2 (pow2 101) c;
    Math.Lemmas.paren_mul_right 2 (pow2 152) d;
    Math.Lemmas.paren_mul_right 2 (pow2 203) e;
    Math.Lemmas.modulo_addition_lemma a 2 ((pow2 50 * b)+(pow2 101 * c)+(pow2 152 * d)+(pow2 203 * e))


private val x_mod_2:
  x:felem ->
  Stack Hacl.UInt64.t
    (requires (fun h -> live h x /\ red_51 (as_seq h x) /\
      (let s = as_seq h x in
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < pow2 255 - 19)))))
    (ensures (fun h0 z h1 -> h0 == h1 /\ live h0 x /\ v z = seval (as_seq h0 x) % 2))
let x_mod_2 x =
  let h = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h x);
  Math.Lemmas.modulo_lemma (let s = as_seq h x in v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4)) Spec.Curve25519.prime;
  lemma_x_mod_2 (v (get h x 0)) (v (get h x 1)) (v (get h x 2)) (v (get h x 3)) (v (get h x 4));
  let x0 = x.(0ul) in
  let z  = x0 &^ Hacl.Cast.uint64_to_sint64 1uL in
  assert_norm(pow2 1 = 2);
  UInt.logand_mask (v x0) 1;
  z



private
val add_sign_spec:
  out:Seq.seq Hacl.UInt8.t{Seq.length out = 32 /\ Hacl.Spec.Endianness.hlittle_endian out < pow2 255} ->
  x:Hacl.UInt64.t{v x < 2} ->
  GTot (s:Seq.seq Hacl.UInt8.t{Seq.length s = 32 /\ Hacl.Spec.Endianness.hlittle_endian s == Hacl.Spec.Endianness.hlittle_endian out + pow2 255 * v x})
#reset-options "--max_fuel 0 --z3rlimit 100"
let add_sign_spec out x =
  assert_norm(pow2 7 = 128);
  assert_norm(pow2 8 = 256);
  assert_norm(pow2 248 = 0x100000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 255 = 0x8000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 256 = 0x10000000000000000000000000000000000000000000000000000000000000000);
  let xbyte = Hacl.Cast.sint64_to_sint8 x in
  Math.Lemmas.modulo_lemma (v x) (pow2 8);
  Seq.lemma_eq_intro out (Seq.append (Seq.slice out 0 31) (Seq.slice out 31 32));
  FStar.Old.Endianness.lemma_little_endian_is_bounded (Hacl.Spec.Endianness.reveal_sbytes (Seq.slice (out) 0 31));
  FStar.Old.Endianness.little_endian_append (Hacl.Spec.Endianness.reveal_sbytes (Seq.slice (out) 0 31)) (Hacl.Spec.Endianness.reveal_sbytes (Seq.slice (out) 31 32));
  let o31 = Seq.index out (31) in
  Seq.lemma_eq_intro (Seq.slice out 31 32) (Seq.create 1 o31);
  FStar.Old.Endianness.little_endian_singleton (Hacl.Spec.Endianness.h8_to_u8 o31);
  assert(Hacl.Spec.Endianness.hlittle_endian (out) == Hacl.Spec.Endianness.hlittle_endian (Seq.slice (out) 0 31)  + pow2 248 * (Hacl.UInt8.v (Seq.index (out) 31)));
  let o31' = Hacl.UInt8.(o31 +%^ (xbyte <<^ 7ul)) in
  Math.Lemmas.modulo_lemma (Hacl.UInt8.v xbyte * pow2 7) (pow2 8);
  assert(Hacl.UInt8.v o31 < 128);
  Math.Lemmas.modulo_lemma (Hacl.UInt8.v o31 + (Hacl.UInt8.v xbyte * pow2 7)) (pow2 8);
  let out' = Seq.upd out 31 o31' in
  Seq.lemma_eq_intro (Seq.slice (out) 0 31) (Seq.slice (out') 0 31);
  Seq.lemma_eq_intro out' (Seq.append (Seq.slice out 0 31) (Seq.slice out' 31 32));
  Seq.lemma_eq_intro (Seq.slice out' 31 32) (Seq.create 1 o31');
  FStar.Old.Endianness.little_endian_singleton (Hacl.Spec.Endianness.h8_to_u8 o31');
  FStar.Old.Endianness.little_endian_append (Hacl.Spec.Endianness.reveal_sbytes (Seq.slice (out') 0 31)) (Hacl.Spec.Endianness.reveal_sbytes (Seq.slice (out') 31 32));
  out'


inline_for_extraction
private
val add_sign:
  out:hint8_p{length out = 32} ->
  x:Hacl.UInt64.t{v x < 2} ->
  Stack unit
    (requires (fun h -> live h out /\ Hacl.Spec.Endianness.hlittle_endian (as_seq h out) < pow2 255))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h1 out /\ modifies_1 out h0 h1
      /\ Hacl.Spec.Endianness.hlittle_endian (as_seq h1 out) == Hacl.Spec.Endianness.hlittle_endian (as_seq h0 out) + pow2 255 * v x))
let add_sign out x =
  let h0 = ST.get() in
  let xbyte = Hacl.Cast.sint64_to_sint8 x in
  let o31 = out.(31ul) in
  out.(31ul) <- Hacl.UInt8.(o31 +%^ (xbyte <<^ 7ul));
  let h1 = ST.get() in
  assert(as_seq h1 out == add_sign_spec (as_seq h0 out) x)


inline_for_extraction
private
val point_compress_:
  tmp:buffer Hacl.UInt64.t{length tmp = 15} ->
  p:Hacl.Impl.Ed25519.ExtPoint.point{disjoint tmp p} ->
  Stack unit
    (requires (fun h -> live h tmp /\ live h p
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.getx p))
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.gety p))
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.getz p))
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.gett p))
      ))
    (ensures (fun h0 _ h1 -> live h0 p /\
      live h1 tmp /\ modifies_1 tmp h0 h1 /\
      (let s = as_seq h1 (Buffer.sub tmp 5ul 5ul) in
       let s' = as_seq h1 (Buffer.sub tmp 10ul 5ul) in
       let x = Hacl.Bignum25519.seval (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx p)) in
       let y = Hacl.Bignum25519.seval (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety p)) in
       let z = Hacl.Bignum25519.seval (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz p)) in
        v (Seq.index s 0) + pow2 51 * v (Seq.index s 1)
        + pow2 102 * v (Seq.index s 2) + pow2 153 * v (Seq.index s 3)
        + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime /\
        v (Seq.index s' 0) + pow2 51 * v (Seq.index s' 1)
        + pow2 102 * v (Seq.index s' 2) + pow2 153 * v (Seq.index s' 3)
        + pow2 204 * v (Seq.index s' 4) < Spec.Curve25519.prime /\
        Hacl.Bignum25519.red_51 s /\
        Hacl.Bignum25519.red_51 s' /\
        Hacl.Bignum25519.seval s == Spec.Curve25519.(x `fmul` (z ** (prime - 2))) /\
        Hacl.Bignum25519.seval s' == Spec.Curve25519.(y `fmul` (z ** (prime - 2))))
    ))
#reset-options "--max_fuel 0 --z3rlimit 100"
let point_compress_ tmp p =
  let h0 = ST.get() in
  let zinv = Buffer.sub tmp 0ul  5ul in
  let x    = Buffer.sub tmp 5ul  5ul in
  let out  = Buffer.sub tmp 10ul 5ul in
  let px   = Hacl.Impl.Ed25519.ExtPoint.getx p in
  let py   = Hacl.Impl.Ed25519.ExtPoint.gety p in
  let pz   = Hacl.Impl.Ed25519.ExtPoint.getz p in
  Hacl.Bignum25519.inverse zinv pz;
  let h1 = ST.get() in
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h1 px);
  Hacl.Bignum25519.lemma_red_513_is_red_5413 (as_seq h1 zinv);
  Hacl.Bignum25519.fmul x px zinv;
  let h2 = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h2 x);
  Hacl.Bignum25519.reduce x;
  let h3 = ST.get() in
  Hacl.Bignum25519.lemma_red_513_is_red_53 (as_seq h3 py);
  Hacl.Bignum25519.fmul out py zinv;
  let h4 = ST.get() in
  Hacl.Bignum25519.reduce out;
  let h5 = ST.get() in
  lemma_modifies_1_trans tmp h0 h1 h2;
  lemma_modifies_1_trans tmp h0 h2 h3;
  lemma_modifies_1_trans tmp h0 h3 h4;
  lemma_modifies_1_trans tmp h0 h4 h5

#reset-options "--max_fuel 0 --z3rlimit 200"

val point_compress:
  out:hint8_p{length out = 32} ->
  p:Hacl.Impl.Ed25519.ExtPoint.point ->
  Stack unit
    (requires (fun h -> live h out /\ live h p
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.getx p))
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.gety p))
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.getz p))
      /\ red_513 (as_seq h (Hacl.Impl.Ed25519.ExtPoint.gett p))
      ))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 p /\
      live h1 out /\ modifies_1 out h0 h1 /\
      h1.[out] == Spec.Ed25519.point_compress (Hacl.Impl.Ed25519.ExtPoint.as_point h0 p)
    ))
let point_compress z p =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let tmp  = create (Hacl.Cast.uint64_to_sint64 0uL) 15ul in
  let zinv = Buffer.sub tmp 0ul  5ul in
  let x    = Buffer.sub tmp 5ul  5ul in
  let out  = Buffer.sub tmp 10ul 5ul in
  (**) let h2 = ST.get() in
  (**) no_upd_fresh h0 h1 (Hacl.Impl.Ed25519.ExtPoint.getz p);
  (**) no_upd_lemma_0 h1 h2 (Hacl.Impl.Ed25519.ExtPoint.getz p);
  (**) Seq.lemma_eq_intro (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz p))
                          (as_seq h2 (Hacl.Impl.Ed25519.ExtPoint.getz p));
  point_compress_ tmp p;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' tmp h1 h2 h3;
  let b = x_mod_2 x in
  Hacl.EC.Format.fcontract_store z out;
  (**) let h4 = ST.get() in
  add_sign z b;
  let h5 = ST.get() in
  (**) lemma_modifies_1_trans z h3 h4 h5;
  (**) lemma_modifies_0_1 z h1 h3 h5;
  (**) FStar.Old.Endianness.lemma_little_endian_inj
    (Hacl.Spec.Endianness.reveal_sbytes (as_seq h5 z))
    (Spec.Ed25519.point_compress (Hacl.Impl.Ed25519.ExtPoint.as_point h0 p));
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 z h0 h1 h5 hfin
