module Hacl.Impl.P256.PointMul

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Impl.P256.Point
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble

module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"

val lemma_cswap2_step: bit:uint64{v bit <= 1} -> p1:uint64 -> p2:uint64 -> Lemma
  (let mask = u64 0 -. bit in
   let dummy = mask &. (p1 ^. p2) in
   let p1' = p1 ^. dummy in
   let p2' = p2 ^. dummy in
   if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)

let lemma_cswap2_step bit p1 p2 =
  let mask = u64 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 64 - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  (* uintv_extensionality dummy (if v bit = 1 then (p1 ^. p2) else u64 0); *)
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1


let conditional_swap (i:uint64) (p:point_seq) (q:point_seq) =
  if uint_v i = 0 then (p, q) else (q, p)


val cswap: bit:uint64{v bit <= 1} -> p:point -> q:point -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ eq_or_disjoint p q /\
    point_inv h p /\ point_inv h q)
  (ensures  fun h0 _ h1 -> modifies (loc p |+| loc q) h0 h1 /\
   (let pr, qr = conditional_swap bit (as_seq h0 p) (as_seq h0 q) in
    as_seq h1 p == pr /\ as_seq h1 q == qr) /\
    (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
    (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q))

[@ CInline]
let cswap bit p1 p2 =
  let open Lib.Sequence in
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 12}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 12}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul 12ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)


(* this piece of code is taken from Hacl.Curve25519 *)
(* changed Endian for Scalar Bit access *)
inline_for_extraction noextract
val scalar_bit: s:lbuffer uint8 32ul -> n:size_t{v n < 256} -> Stack uint64
  (requires fun h0 -> live h0 s)
  (ensures  fun h0 r h1 -> h0 == h1 /\ r == S.ith_bit (as_seq h0 s) (v n) /\ v r <= 1)

let scalar_bit s n =
  let h0 = ST.get () in
  mod_mask_lemma ((LSeq.index (as_seq h0 s) (31 - v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(31ul -. n /. 8ul) >>. (n %. 8ul)) &. u8 1)


inline_for_extraction noextract
val montgomery_ladder_step1: p:point -> q:point -> tmp:lbuffer uint64 (size 88) -> Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h tmp /\
    disjoint p q /\ disjoint p tmp /\ disjoint q tmp /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tmp) h0 h1 /\
    point_inv h1 p /\ point_inv h1 q /\
    (SM.from_mont_point (as_point_nat h1 p), SM.from_mont_point (as_point_nat h1 q)) ==
     S._ml_step1
      (SM.from_mont_point (as_point_nat h0 p)) (SM.from_mont_point (as_point_nat h0 q)))

let montgomery_ladder_step1 r0 r1 tmp =
  point_add r0 r1 r1 tmp;
  point_double r0 r0 tmp


inline_for_extraction noextract
val montgomery_ladder_step:
    p:point -> q:point -> tmp:lbuffer uint64 88ul
  -> scalar:lbuffer uint8 32ul
  -> i:size_t{v i < 256} ->
  Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h tmp /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tmp; loc scalar] /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tmp) h0 h1 /\
    point_inv h1 p /\ point_inv h1 q /\
    (SM.from_mont_point (as_point_nat h1 p), SM.from_mont_point (as_point_nat h1 q)) ==
     S._ml_step (as_seq h0 scalar) (v i)
      (SM.from_mont_point (as_point_nat h0 p), SM.from_mont_point (as_point_nat h0 q)))

let montgomery_ladder_step r0 r1 tmp scalar i =
  let bit0 = 255ul -. i in
  assert (v bit0 = 255 - v i);
  let bit = scalar_bit scalar bit0 in
  cswap bit r0 r1;
  montgomery_ladder_step1 r0 r1 tmp;
  cswap bit r0 r1


val montgomery_ladder: p:point -> q:point
  -> scalar:lbuffer uint8 32ul
  -> tmp:lbuffer uint64 88ul ->
  Stack unit
  (requires fun h ->
    live h p /\ live h q /\ live h scalar /\  live h tmp /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tmp; loc scalar] /\
    point_inv h p /\ point_inv h q)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tmp) h0 h1 /\
    (point_inv h1 p /\ point_inv h1 q /\
    (let p1 = SM.from_mont_point (as_point_nat h1 p) in
     let q1 = SM.from_mont_point (as_point_nat h1 q) in
     let rN, qN =
       S.montgomery_ladder_spec (as_seq h0 scalar)
         (SM.from_mont_point (as_point_nat h0 p), SM.from_mont_point (as_point_nat h0 q)) in
       rN == p1 /\ qN == q1)))

[@CInline]
let montgomery_ladder p q scalar tmp =
  let h0 = ST.get() in

  [@inline_let]
  let spec_ml h0 = S._ml_step (as_seq h0 scalar) in

  [@inline_let]
  let acc (h:mem) : GTot (tuple2 S.jacob_point S.jacob_point) =
  (SM.from_mont_point(as_point_nat h p), SM.from_mont_point(as_point_nat h q))  in

  Lib.LoopCombinators.eq_repeati0 256 (spec_ml h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) =
    point_inv h p /\ point_inv h q /\
    modifies3 p q tmp h0 h /\
    acc h == Lib.LoopCombinators.repeati i (spec_ml h0) (acc h0) in

  Lib.Loops.for 0ul 256ul inv
    (fun i ->
      montgomery_ladder_step p q tmp scalar i;
      Lib.LoopCombinators.unfold_repeati 256 (spec_ml h0) (acc h0) (uint_v i)
    )


val lemma_point_to_domain: h0:mem -> h1:mem -> p:point -> res:point ->  Lemma
  (requires
    point_inv h0 p /\
    point_x_as_nat h1 res == SM.to_mont (point_x_as_nat h0 p) /\
    point_y_as_nat h1 res == SM.to_mont (point_y_as_nat h0 p) /\
    point_z_as_nat h1 res == SM.to_mont (point_z_as_nat h0 p))
  (ensures (SM.from_mont_point (as_point_nat h1 res) == as_point_nat h0 p))

let lemma_point_to_domain h0 h1 p res =
  SM.lemma_to_from_mont_id (point_x_as_nat h0 p);
  SM.lemma_to_from_mont_id (point_y_as_nat h0 p);
  SM.lemma_to_from_mont_id (point_z_as_nat h0 p)


val scalarMultiplicationWithoutNorm: p:point -> res:point -> scalar:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h p /\ live h res /\ live h scalar /\
    disjoint p res /\ disjoint scalar res /\ disjoint p scalar /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc res) h0 h1 /\
    point_inv h1 res /\
    SM.from_mont_point (as_point_nat h1 res) ==
      fst (S.montgomery_ladder_spec (as_seq h0 scalar) (S.point_at_inf, as_point_nat h0 p)))

[@CInline]
let scalarMultiplicationWithoutNorm p res scalar =
  push_frame ();
  let tmp = create 100ul (u64 0) in
  let q = sub tmp 0ul 12ul in
  make_point_at_inf q;

  let h0 = ST.get () in
  point_to_mont p res;
  let h1 = ST.get () in
  lemma_point_to_domain h0 h1 p res;

  let buff = sub tmp 12ul 88ul in
  montgomery_ladder q res scalar buff;
  let h3 = ST.get () in
  copy res q;
  pop_frame ()


[@CInline]
let point_mul res p scalar =
  push_frame ();
  let tmp = create_point () in
  copy_point p tmp;

  let bytes_scalar = create 32ul (u8 0) in
  bn_to_bytes_be4 scalar bytes_scalar;

  scalarMultiplicationWithoutNorm tmp res bytes_scalar;
  //point_from_mont res res;
  pop_frame ()


[@CInline]
let point_mul_g res scalar =
  push_frame ();
  let bytes_scalar = create 32ul (u8 0) in
  bn_to_bytes_be4 scalar bytes_scalar;

  let g = create_point () in
  make_base_point g;

  let tmp = create 100ul (u64 0) in
  let q = sub tmp 0ul 12ul in
  make_point_at_inf q;

  let buff = sub tmp 12ul 88ul in
  montgomery_ladder q g bytes_scalar buff;
  let h3 = ST.get () in
  copy_point q res;
  //point_from_mont q res;
  pop_frame ()


[@CInline]
let point_mul_bytes res p scalar =
  push_frame ();
  let s_q = create_felem () in
  bn_from_bytes_be4 scalar s_q;
  point_mul res p s_q;
  norm_jacob_point res res;
  pop_frame ()


[@CInline]
let point_mul_g_bytes res scalar =
  push_frame ();
  let s_q = create_felem () in
  bn_from_bytes_be4 scalar s_q;
  point_mul_g res s_q;
  norm_jacob_point res res;
  pop_frame ()


[@CInline]
let point_mul_double_g res scalar1 scalar2 p =
  push_frame ();
  let sg1 = create_point () in
  let sp2 = create_point () in
  let tmp = create (size 88) (u64 0) in
  let h0 = ST.get () in
  point_mul_g sg1 scalar1; // sg1 = [scalar1]G
  point_mul sp2 p scalar2; // sp2 = [scalar2]P
  let h1 = ST.get () in
  assert (SM.from_mont_point (as_point_nat h1 sg1) ==
    S.point_mul_g (as_nat h0 scalar1));
  assert (SM.from_mont_point (as_point_nat h1 sp2) ==
    S.point_mul (as_nat h0 scalar2) (as_point_nat h0 p));

  let is_points_eq = is_point_eq_vartime sg1 sp2 in
  assert (is_points_eq =
    (S.norm_jacob_point (SM.from_mont_point (as_point_nat h1 sg1)) =
     S.norm_jacob_point (SM.from_mont_point (as_point_nat h1 sp2))));

  begin
  if is_points_eq
  then point_double sg1 res tmp
  else point_add sg1 sp2 res tmp end;
  pop_frame ()
