module Hacl.Impl.P256.PointMul

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.Lemmas
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


inline_for_extraction noextract
val montgomery_ladder: #buf_type: buftype->  p: point -> q: point ->
  scalar: lbuffer_t buf_type uint8 (size 32) ->
  tempBuffer:  lbuffer uint64 (size 88)  ->
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h scalar /\  live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\

    as_nat h (gsub q (size 0) (size 4)) < S.prime /\
    as_nat h (gsub q (size 4) (size 4)) < S.prime /\
    as_nat h (gsub q (size 8) (size 4)) < S.prime )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\
    (
      as_nat h1 (gsub p (size 0) (size 4)) < S.prime /\
      as_nat h1 (gsub p (size 4) (size 4)) < S.prime /\
      as_nat h1 (gsub p (size 8) (size 4)) < S.prime /\

      as_nat h1 (gsub q (size 0) (size 4)) < S.prime /\
      as_nat h1 (gsub q (size 4) (size 4)) < S.prime /\
      as_nat h1 (gsub q (size 8) (size 4)) < S.prime /\


      (
	let p1 = fromDomainPoint(as_point_nat h1 p) in
	let q1 = fromDomainPoint(as_point_nat h1 q) in
	let rN, qN = S.montgomery_ladder_spec (as_seq h0 scalar)
	  (
	    fromDomainPoint(as_point_nat h0 p),
	    fromDomainPoint(as_point_nat h0 q)
	  ) in
	rN == p1 /\ qN == q1
      )
   )
 )

let montgomery_ladder #a p q scalar tempBuffer =
  let h0 = ST.get() in


  [@inline_let]
  let spec_ml h0 = S._ml_step (as_seq h0 scalar) in

  [@inline_let]
  let acc (h:mem) : GTot (tuple2 S.jacob_point S.jacob_point) =
  (fromDomainPoint(as_point_nat h p), fromDomainPoint(as_point_nat h q))  in

  Lib.LoopCombinators.eq_repeati0 256 (spec_ml h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) =
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime /\

    as_nat h (gsub q (size 0) (size 4)) < S.prime /\
    as_nat h (gsub q (size 4) (size 4)) < S.prime /\
    as_nat h (gsub q (size 8) (size 4)) < S.prime /\
    modifies3 p q tempBuffer h0 h   /\
    acc h == Lib.LoopCombinators.repeati i (spec_ml h0) (acc h0)

    in

  Lib.Loops.for 0ul 256ul inv
    (fun i -> let h2 = ST.get() in
      montgomery_ladder_step p q tempBuffer scalar i;
      Lib.LoopCombinators.unfold_repeati 256 (spec_ml h0) (acc h0) (uint_v i)
    )


val lemma_point_to_domain: h0: mem -> h1: mem ->  p: point -> result: point ->  Lemma
   (requires (point_x_as_nat h0 p < S.prime /\ point_y_as_nat h0 p < S.prime /\ point_z_as_nat h0 p < S.prime /\
       point_x_as_nat h1 result == toDomain_ (point_x_as_nat h0 p) /\
       point_y_as_nat h1 result == toDomain_ (point_y_as_nat h0 p) /\
       point_z_as_nat h1 result == toDomain_ (point_z_as_nat h0 p)
     )
   )
   (ensures (fromDomainPoint(as_point_nat h1 result) == as_point_nat h0 p))

let lemma_point_to_domain h0 h1 p result =
  let (x, y, z) = as_point_nat h1 result in ()


val lemma_pif_to_domain: h: mem ->  p: point -> Lemma
  (requires (point_x_as_nat h p == 0 /\ point_y_as_nat h p == 0 /\ point_z_as_nat h p == 0))
  (ensures (fromDomainPoint (as_point_nat h p) == as_point_nat h p))

let lemma_pif_to_domain h p =
  let (x, y, z) = as_point_nat h p in
  let (x3, y3, z3) = fromDomainPoint (x, y, z) in
  lemmaFromDomain x;
  lemmaFromDomain y;
  lemmaFromDomain z;
  lemma_multiplication_not_mod_prime x;
  lemma_multiplication_not_mod_prime y;
  lemma_multiplication_not_mod_prime z


val lemma_coord: h3: mem -> q: point -> Lemma (
   let (r0, r1, r2) = fromDomainPoint(as_point_nat h3 q) in
	let xD = fromDomain_ (point_x_as_nat h3 q) in
	let yD = fromDomain_ (point_y_as_nat h3 q) in
	let zD = fromDomain_ (point_z_as_nat h3 q) in
    r0 == xD /\ r1 == yD /\ r2 == zD)

let lemma_coord h3 q = ()


inline_for_extraction
val scalarMultiplication_t: #t:buftype -> p: point -> result: point ->
  scalar: lbuffer_t t uint8 (size 32) ->
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h ->
      live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    as_nat h (gsub p (size 0) (size 4)) < S.prime /\
    as_nat h (gsub p (size 4) (size 4)) < S.prime /\
    as_nat h (gsub p (size 8) (size 4)) < S.prime
    )
  (ensures fun h0 _ h1 ->
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\

    as_nat h1 (gsub result (size 0) (size 4)) < S.prime /\
    as_nat h1 (gsub result (size 4) (size 4)) < S.prime /\
    as_nat h1 (gsub result (size 8) (size 4)) < S.prime /\

    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in
      let (xN, yN, zN) = S.scalar_multiplication (as_seq h0 scalar) (as_point_nat h0 p) in
      x3 == xN /\ y3 == yN /\ z3 == zN
  )
)


let scalarMultiplication_t #t p result scalar tempBuffer  =
    let h0 = ST.get() in
  let q = sub tempBuffer (size 0) (size 12) in
  make_point_at_inf q;
  let buff = sub tempBuffer (size 12) (size 88) in
  point_to_mont p result;
    let h2 = ST.get() in
  montgomery_ladder q result scalar buff;
    let h3 = ST.get() in
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
  norm_jacob_point q result;
    lemma_coord h3 q


let scalarMultiplicationL = scalarMultiplication_t #MUT

let scalarMultiplicationI = scalarMultiplication_t #IMMUT
let scalarMultiplicationC = scalarMultiplication_t #CONST

let scalarMultiplication #buf_type p result scalar tempBuffer =
  match buf_type with
  |MUT -> scalarMultiplicationL p result scalar tempBuffer
  |IMMUT -> scalarMultiplicationI p result scalar tempBuffer
  |CONST -> scalarMultiplicationC p result scalar tempBuffer



let scalarMultiplicationWithoutNorm p result scalar tempBuffer =
  let h0 = ST.get() in
  let q = sub tempBuffer (size 0) (size 12) in
  make_point_at_inf q;
  let buff = sub tempBuffer (size 12) (size 88) in
  point_to_mont p result;
    let h2 = ST.get() in
  montgomery_ladder q result scalar buff;
  copy_point q result;
    let h3 = ST.get() in
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q


let secretToPublic result scalar tempBuffer =
  push_frame();
       let basePoint = create (size 12) (u64 0) in
    make_base_point basePoint;
      let q = sub tempBuffer (size 0) (size 12) in
      let buff = sub tempBuffer (size 12) (size 88) in
    make_point_at_inf q;
      let h1 = ST.get() in
      lemma_pif_to_domain h1 q;
    montgomery_ladder q basePoint scalar buff;
    norm_jacob_point q result;
  pop_frame()


let secretToPublicWithoutNorm result scalar tempBuffer =
    push_frame();
      let basePoint = create (size 12) (u64 0) in
    make_base_point basePoint;
      let q = sub tempBuffer (size 0) (size 12) in
      let buff = sub tempBuffer (size 12) (size 88) in
    make_point_at_inf q;
      let h1 = ST.get() in
      lemma_pif_to_domain h1 q;
    montgomery_ladder q basePoint scalar buff;
    copy_point q result;
  pop_frame()
