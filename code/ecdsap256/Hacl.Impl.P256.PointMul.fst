module Hacl.Impl.P256.PointMul

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field
open Hacl.Spec.P256.Math
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble
open Hacl.Impl.P256.Finv
open Hacl.Impl.P256.Point

module S = Spec.P256
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

#set-options "--z3rlimit 100 --fuel 0 --ifuel 0"


(*This code is taken from Curve25519, written by Polubelova M *)
val lemma_cswap2_step:
    bit:uint64{v bit <= 1}
  -> p1:uint64
  -> p2:uint64
  -> Lemma (
      let mask = u64 0 -. bit in
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

(* </> *)

val lemma_scalar_ith: sc:BSeq.lbytes 32 -> k:nat{k < 32} ->
  Lemma (v (LSeq.index sc k) == BSeq.nat_from_intseq_le sc / pow2 (8 * k) % pow2 8)

let lemma_scalar_ith sc k =
  BSeq.index_nat_to_intseq_le #U8 #SEC 32 (BSeq.nat_from_intseq_le sc) k;
  BSeq.nat_from_intseq_le_inj sc (BSeq.nat_to_intseq_le 32 (BSeq.nat_from_intseq_le sc))


val lemma_euclidian_for_ithbit: k: nat -> i: nat
  -> Lemma (k / (pow2 (8 * (i / 8)) * pow2 (i % 8)) == k / pow2 i)

let lemma_euclidian_for_ithbit k i =
  Math.Lib.lemma_div_def i 8;
  Math.Lemmas.pow2_plus (8 * (i / 8)) (i % 8)


val ith_bit: k:BSeq.lbytes 32 -> i:nat{i < 256}
  -> t:uint64 {(v t == 0 \/ v t == 1) /\ v t == BSeq.nat_from_intseq_le k / pow2 i % 2}

let ith_bit k i =
  let open Lib.Sequence in
  let q = i / 8 in
  let r = i % 8 in
  let tmp1 = k.[q] >>. (size r) in
  let tmp2 = tmp1 &. u8 1 in
  let res = to_u64 tmp2 in
  logand_le tmp1 (u8 1);
  logand_mask tmp1 (u8 1) 1;
  lemma_scalar_ith k q;
  let k = BSeq.nat_from_intseq_le k in
  Math.Lemmas.pow2_modulo_division_lemma_1 (k / pow2 (8 * (i / 8))) (i % 8) 8;
  Math.Lemmas.division_multiplication_lemma k (pow2 (8 * (i / 8))) (pow2 (i % 8));
  lemma_euclidian_for_ithbit k i;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (k / pow2 i) 1 (8 - (i % 8));
  res


// TODO: rename
let point_prime = p:point_seq{point_inv_seq p}

val swap: p: point_prime -> q: point_prime -> Tot (r: tuple2 point_prime point_prime {let pNew, qNew = r in
  pNew == q /\ qNew == p})

let swap p q = (q, p)


val conditional_swap: i: uint64 -> p: point_prime -> q: point_prime -> Tot (r: tuple2 point_prime point_prime
  {
    let pNew, qNew = r in
    if uint_v i = 0 then pNew == p /\ qNew == q
    else
      let p1, q1 = swap p q in
      p1 == pNew /\ q1 == qNew
 }
)

let conditional_swap i p q =
  if uint_v i = 0 then
    (p, q)
  else
    (q, p)


[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:point -> q:point
  -> Stack unit
    (requires fun h ->
      live h p /\ live h q /\ (disjoint p q \/ p == q) /\

      as_nat h (gsub p (size 0) (size 4)) < S.prime /\
      as_nat h (gsub p (size 4) (size 4)) < S.prime /\
      as_nat h (gsub p (size 8) (size 4)) < S.prime /\

      as_nat h (gsub q (size 0) (size 4)) < S.prime /\
      as_nat h (gsub q (size 4) (size 4)) < S.prime /\
      as_nat h (gsub q (size 8) (size 4)) < S.prime
)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
      (let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in
  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in
  let condP0, condP1 = conditional_swap bit pBefore qBefore  in
  condP0 == pAfter /\ condP1 == qAfter) /\

      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q))


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
val scalar_bit:
    #buf_type: buftype ->
    s:lbuffer_t buf_type uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\ r == ith_bit (as_seq h0 s) (v n) /\ v r <= 1)

let scalar_bit #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (31 - v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(31ul -. n /. 8ul) >>. (n %. 8ul)) &. u8 1)


inline_for_extraction noextract
val montgomery_ladder_step1: p: point -> q: point ->tempBuffer: lbuffer uint64 (size 88) -> Stack unit
  (requires fun h -> live h p /\ live h q /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer] /\

    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\

    as_nat h (gsub q (size 0) (size 4)) < S.prime /\
    as_nat h (gsub q (size 4) (size 4)) < S.prime /\
    as_nat h (gsub q (size 8) (size 4)) < S.prime

  )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+|  loc tempBuffer) h0 h1 /\
    (
      let pX = as_nat h0 (gsub p (size 0) (size 4)) in
      let pY = as_nat h0 (gsub p (size 4) (size 4)) in
      let pZ = as_nat h0 (gsub p (size 8) (size 4)) in

      let qX = as_nat h0 (gsub q (size 0) (size 4)) in
      let qY = as_nat h0 (gsub q (size 4) (size 4)) in
      let qZ = as_nat h0 (gsub q (size 8) (size 4)) in

      let r0X = as_nat h1 (gsub p (size 0) (size 4)) in
      let r0Y = as_nat h1 (gsub p (size 4) (size 4)) in
      let r0Z = as_nat h1 (gsub p (size 8) (size 4)) in

      let r1X = as_nat h1 (gsub q (size 0) (size 4)) in
      let r1Y = as_nat h1 (gsub q (size 4) (size 4)) in
      let r1Z = as_nat h1 (gsub q (size 8) (size 4)) in


      let (rN0X, rN0Y, rN0Z), (rN1X, rN1Y, rN1Z) = S._ml_step1 (fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ) (fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ) in

      fromDomain_ r0X == rN0X /\ fromDomain_ r0Y == rN0Y /\ fromDomain_ r0Z == rN0Z /\
      fromDomain_ r1X == rN1X /\ fromDomain_ r1Y == rN1Y /\ fromDomain_ r1Z == rN1Z /\

      r0X < S.prime /\ r0Y < S.prime /\ r0Z < S.prime /\
      r1X < S.prime /\ r1Y < S.prime /\ r1Z < S.prime
  )
)


let montgomery_ladder_step1 r0 r1 tempBuffer =
  point_add r0 r1 r1 tempBuffer;
  point_double r0 r0 tempBuffer


val lemma_step: i: size_t {uint_v i < 256} -> Lemma  (uint_v ((size 255) -. i) == 255 - (uint_v i))
let lemma_step i = ()


inline_for_extraction noextract
val montgomery_ladder_step: #buf_type: buftype->
  p: point -> q: point ->tempBuffer: lbuffer uint64 (size 88) ->
  scalar: lbuffer_t buf_type uint8 (size 32) ->
  i:size_t{v i < 256} ->
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\

    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\

    as_nat h (gsub q (size 0) (size 4)) < S.prime /\
    as_nat h (gsub q (size 4) (size 4)) < S.prime /\
    as_nat h (gsub q (size 8) (size 4)) < S.prime
  )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\
    (

      let pX = as_nat h0 (gsub p (size 0) (size 4)) in
      let pY = as_nat h0 (gsub p (size 4) (size 4)) in
      let pZ = as_nat h0 (gsub p (size 8) (size 4)) in

      let qX = as_nat h0 (gsub q (size 0) (size 4)) in
      let qY = as_nat h0 (gsub q (size 4) (size 4)) in
      let qZ = as_nat h0 (gsub q (size 8) (size 4)) in

      let r0X = as_nat h1 (gsub p (size 0) (size 4)) in
      let r0Y = as_nat h1 (gsub p (size 4) (size 4)) in
      let r0Z = as_nat h1 (gsub p (size 8) (size 4)) in

      let r1X = as_nat h1 (gsub q (size 0) (size 4)) in
      let r1Y = as_nat h1 (gsub q (size 4) (size 4)) in
      let r1Z = as_nat h1 (gsub q (size 8) (size 4)) in

      let (rN0X, rN0Y, rN0Z), (rN1X, rN1Y, rN1Z) = S._ml_step (as_seq h0 scalar) (uint_v i) ((fromDomain_ pX, fromDomain_ pY, fromDomain_ pZ), (fromDomain_ qX, fromDomain_ qY, fromDomain_ qZ)) in

      fromDomain_ r0X == rN0X /\ fromDomain_ r0Y == rN0Y /\ fromDomain_ r0Z == rN0Z /\
      fromDomain_ r1X == rN1X /\ fromDomain_ r1Y == rN1Y /\ fromDomain_ r1Z == rN1Z /\

      r0X < S.prime /\ r0Y < S.prime /\ r0Z < S.prime /\
      r1X < S.prime /\ r1Y < S.prime /\ r1Z < S.prime
    )
  )


let montgomery_ladder_step #buf_type r0 r1 tempBuffer scalar i =
  let bit0 = (size 255) -. i in
  let bit = scalar_bit scalar bit0 in
  cswap bit r0 r1;
  montgomery_ladder_step1 r0 r1 tempBuffer;
  cswap bit r0 r1;
    lemma_step i


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
    (let p1 = fromDomainPoint (as_point_nat h1 p) in
     let q1 = fromDomainPoint (as_point_nat h1 q) in
     let rN, qN =
       S.montgomery_ladder_spec (as_seq h0 scalar)
         (fromDomainPoint (as_point_nat h0 p), fromDomainPoint (as_point_nat h0 q)) in
       rN == p1 /\ qN == q1)))

[@CInline]
let montgomery_ladder p q scalar tmp =
  let h0 = ST.get() in

  [@inline_let]
  let spec_ml h0 = S._ml_step (as_seq h0 scalar) in

  [@inline_let]
  let acc (h:mem) : GTot (tuple2 S.jacob_point S.jacob_point) =
  (fromDomainPoint(as_point_nat h p), fromDomainPoint(as_point_nat h q))  in

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
    point_x_as_nat h1 res == toDomain_ (point_x_as_nat h0 p) /\
    point_y_as_nat h1 res == toDomain_ (point_y_as_nat h0 p) /\
    point_z_as_nat h1 res == toDomain_ (point_z_as_nat h0 p))
  (ensures (fromDomainPoint (as_point_nat h1 res) == as_point_nat h0 p))

let lemma_point_to_domain h0 h1 p res =
  SM.lemmaToDomainAndBackIsTheSame (point_x_as_nat h0 p);
  SM.lemmaToDomainAndBackIsTheSame (point_y_as_nat h0 p);
  SM.lemmaToDomainAndBackIsTheSame (point_z_as_nat h0 p)


val scalarMultiplicationWithoutNorm: p:point -> res:point -> scalar:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h p /\ live h res /\ live h scalar /\
    disjoint p res /\ disjoint scalar res /\ disjoint p scalar /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc res) h0 h1 /\
    point_inv h1 res /\
    SM.fromDomainPoint (as_point_nat h1 res) ==
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
  assert (SM.fromDomainPoint (as_point_nat h1 sg1) ==
    S.point_mul_g (as_nat h0 scalar1));
  assert (SM.fromDomainPoint (as_point_nat h1 sp2) ==
    S.point_mul (as_nat h0 scalar2) (as_point_nat h0 p));

  let is_points_eq = is_point_eq_vartime sg1 sp2 in
  assert (is_points_eq =
    (S.norm_jacob_point (SM.fromDomainPoint (as_point_nat h1 sg1)) =
     S.norm_jacob_point (SM.fromDomainPoint (as_point_nat h1 sp2))));

  begin
  if is_points_eq
  then point_double sg1 res tmp
  else point_add sg1 sp2 res tmp end;
  pop_frame ()
