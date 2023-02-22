module Hacl.Impl.P256.Finv

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Math.Lemmas

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum
open Hacl.Impl.P256.Field

open Spec.P256.MontgomeryMultiplication
friend Spec.P256.MontgomeryMultiplication

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 200"

#reset-options "--z3rlimit 500"

val fsquarePowN: n: size_t -> a: felem -> Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256))
  (ensures (fun h0 _ h1 ->
    modifies (loc a) h0 h1 /\  as_nat h1 a < prime256 /\
    (let k = fromDomain_(as_nat h0 a) in as_nat h1 a = toDomain_ (pow k (pow2 (v n)))))
  )

let fsquarePowN n a =
  let h0 = ST.get() in
  lemmaFromDomainToDomain (as_nat h0 a);
  assert_norm (pow2 0 == 1);
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k = fromDomain_ (as_nat h0 a) in
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\
    as_nat h1 a < prime256 /\ live h1 a /\ modifies1 a h0 h1  in
  power_one (fromDomain_ (as_nat h0 a));
  Lib.Loops.for (size 0) n (inv h0) (fun x ->
    let h0_ = ST.get() in
     fsqr a a;
     let k = fromDomain_ (as_nat h0 a) in
     inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));
     lemmaFromDomainToDomainModuloPrime (let k = fromDomain_ (as_nat h0 a) in pow k (pow2 (v x)));
     modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256;
     pow_plus k  (pow2 (v x)) (pow2 (v x ));
     pow2_double_sum (v x);
     inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)))
  )


val fsquarePowNminusOne: n: size_t -> a: felem -> tempBuffer: felem -> Stack unit
  (requires (fun h -> live h a /\ live h tempBuffer /\ as_nat h a < prime256 /\ disjoint a tempBuffer))
  (ensures (fun h0 _ h1 ->
    as_nat h1 a < prime256 /\ as_nat h1 tempBuffer < prime256 /\
    modifies (loc a |+| loc tempBuffer) h0 h1 /\
    (
      let k = fromDomain_ (as_nat h0 a) in
      as_nat h1 a = toDomain_ (pow k (pow2 (v n))) /\ as_nat h1 tempBuffer = toDomain_ (pow k (pow2 (v n) -1 )))
    )
   )

let fsquarePowNminusOne n a b =
  let h0 = ST.get() in
  assert_norm(prime256 > 3);
  Lib.Buffer.upd b (size 0) (u64 1);
  Lib.Buffer.upd b (size 1) (u64 18446744069414584320);
  Lib.Buffer.upd b (size 2) (u64 18446744073709551615);
  Lib.Buffer.upd b (size 3) (u64 4294967294);

  let one = (u64 1, u64 18446744069414584320, u64 18446744073709551615, u64 4294967294) in
      lemmaFromDomainToDomain (as_nat h0 a);
      lemmaToDomain 1;
      assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 = 26959946660873538059280334323183841250350249843923952699046031785985);
      assert_norm (pow2 256 % prime256 == 26959946660873538059280334323183841250350249843923952699046031785985);
      assert_norm (as_nat4 one = toDomain_(1));

  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k = fromDomain_(as_nat h0 a) in
    as_nat h1 b = toDomain_ (pow k (pow2 i - 1)) /\ as_nat h1 a < prime256 /\ live h1 a /\
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\ as_nat h1 b < prime256 /\ live h1 b /\ modifies (loc a |+| loc b) h0 h1 in
  Lib.Loops.for (size 0) n (inv h0) (fun x ->
    let h0_ = ST.get() in
    fmul b a b;
    fsqr a a;
    let k = fromDomain_ (as_nat h0 a) in
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ b) * fromDomain_ (as_nat h0_ a));
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));

    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x) -1 ));
    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x)));
    modulo_distributivity_mult (pow k (pow2 (v x) - 1)) (pow k (pow2 (v x))) prime256;
    modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256;

    pow_plus k (pow2 (v x) -1 ) (pow2 (v x));
    pow_plus k (pow2 (v x)) (pow2 (v x));
    pow2_double_sum (v x);

    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)));
    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1) - 1))
)


inline_for_extraction noextract
val norm_part_one: a: felem -> tempBuffer: lbuffer uint64 (size 8) ->
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime256)
  (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime256 /\
  (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 32 - 1) * pow2 224) % prime256))))

let norm_part_one a tempBuffer =
    let h0 = ST.get() in
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in

  fsquarePowNminusOne (size 32) buffer_a buffer_b;
  fsquarePowN (size 224) buffer_b;

  let k = fromDomain_ (as_nat h0 a) in
  lemmaFromDomainToDomainModuloPrime (pow k (pow2 32 - 1));
  let k_powers = pow k (pow2 32 - 1) in
  let k_prime = k_powers % prime256 in
  inDomain_mod_is_not_mod (pow k_prime (pow2 224));
  power_distributivity k_powers (pow2 224) prime256;
  power_mult k (pow2 32 - 1) (pow2 224)


inline_for_extraction noextract
val norm_part_two: a: felem -> tempBuffer: lbuffer uint64 (size 4) ->
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime256)
  (ensures fun h0 _ h1 -> as_nat h1 tempBuffer < prime256 /\ modifies1 tempBuffer h0 h1 /\
    (let k = fromDomain_ (as_nat h0 a) in as_nat h1 tempBuffer = toDomain_(pow k (pow2 192) % prime256)))

let norm_part_two a tempBuffer =
  let h0 = ST.get() in
  Lib.Buffer.copy tempBuffer a;
  fsquarePowN (size 192) tempBuffer;
  let k = fromDomain_ (as_nat h0 a) in
  inDomain_mod_is_not_mod (pow k (pow2 192))


inline_for_extraction noextract
val norm_part_three:a: felem -> tempBuffer: lbuffer uint64 (size 8) ->
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\
   as_nat h a < prime256)
  (ensures fun h0 _ h1 ->  modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime256
    /\ (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 94 - 1) * pow2 2) % prime256))))

let norm_part_three a tempBuffer =
  let h0 = ST.get() in
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in

  fsquarePowNminusOne (size 94) buffer_a buffer_b;
  fsquarePowN (size 2) buffer_b;

  let k = fromDomain_ (as_nat h0 a) in
  lemmaFromDomainToDomainModuloPrime (pow k (pow2 94 - 1));
  let k_powers = pow k (pow2 94 - 1) in
  let k_prime = k_powers % prime256 in
  inDomain_mod_is_not_mod (pow k_prime (pow2 2));
  power_distributivity k_powers (pow2 2) prime256;
  power_mult k (pow2 94 - 1) (pow2 2)


val lemma_inDomainModulo: a: nat -> b: nat -> Lemma ((toDomain_ ((a % prime256) * (b % prime256) % prime256) = toDomain_ (a * b % prime256)))
let lemma_inDomainModulo a b =
  lemma_mod_mul_distr_l a (b % prime256) prime256;
  lemma_mod_mul_distr_r a b prime256


val big_power: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (pow a b * pow a c * pow a d * pow a e = pow a (b + c + d + e))
let big_power a b c d e =
  assert(pow a b * pow a c * pow a d * pow a e = (pow a b * pow a c) * (pow a d * pow a e));
  pow_plus a b c;
  pow_plus a d e;
  pow_plus a (b + c) (d + e)


val lemma_mul_nat: a: nat -> b: nat -> Lemma (a * b >= 0)
let lemma_mul_nat a b = ()


#reset-options " --z3rlimit 200"
let exponent a result tempBuffer =
  let h0 = ST.get () in
  let buffer_norm_1 = Lib.Buffer.sub  tempBuffer (size 0) (size 8) in
    let buffer_result1 = Lib.Buffer.sub tempBuffer (size 4) (size 4) in
  let buffer_result2 = Lib.Buffer.sub tempBuffer (size 8) (size 4) in
  let buffer_norm_3 = Lib.Buffer.sub tempBuffer (size 12) (size 8) in
    let buffer_result3 = Lib.Buffer.sub tempBuffer (size 16) (size 4) in

  norm_part_one a buffer_norm_1;
  norm_part_two a buffer_result2;
  norm_part_three a buffer_norm_3;

    let h1 = ST.get() in
  fmul buffer_result1 buffer_result2 buffer_result1;
    let h2 = ST.get() in
  fmul buffer_result1 buffer_result3 buffer_result1;
    let h3 = ST.get() in
  fmul buffer_result1 a buffer_result1;
    let h4 = ST.get() in
  copy result buffer_result1;
    let h5 = ST.get() in
  assert_norm ((pow2 32 - 1) * pow2 224 >= 0);
  assert_norm (pow2 192 >= 0);
  assert_norm ((pow2 94 - 1) * pow2 2 >= 0);


  let k = fromDomain_ (as_nat h0 a) in
  let power1 = pow k ((pow2 32 - 1) * pow2 224) in
  let power2 = pow k (pow2 192) in
  let power3 = pow k ((pow2 94 - 1) * pow2 2) in
  let power4 = pow k 1 in

  lemma_mul_nat power1 power2;

  lemma_inDomainModulo power1 power2;
  lemma_inDomainModulo (power1 * power2) power3;
  inDomain_mod_is_not_mod (((power1 * power2 * power3) % prime256 * power4));
  lemma_mod_mul_distr_l (power1 * power2 * power3) power4 prime256;
  big_power k ((pow2 32 - 1) * pow2 224) (pow2 192) ((pow2 94 -1 ) * pow2 2) 1;
  assert_norm(((pow2 32 - 1) * pow2 224 + pow2 192 + (pow2 94 -1 ) * pow2 2 + 1) = prime256 - 2)


//-----------------------------------------------

[@ CInline]
val cswap: bit:uint64{v bit <= 1} -> p:felem -> q:felem
  -> Stack unit
    (requires fun h ->
      as_nat h p < prime /\ as_nat h q < prime /\
      live h p /\ live h q /\ eq_or_disjoint p q)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
	(
	  let (r0, r1) = conditional_swap_pow bit (as_nat h0 p) (as_nat h0 q) in
	  let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in
	  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in
	  as_nat h1 p < prime /\ as_nat h1 q < prime /\
      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q)))


let cswap bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in
  let open Lib.Sequence in
  [@ inline_let]
  let inv h1 (i:nat{i <= 4}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 4}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul 4ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)


inline_for_extraction noextract
val upload_one_montg_form: b: felem -> Stack unit
  (requires fun h -> live h b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ as_nat h1 b == toDomain_ (1) /\ as_nat h1 b < prime)

let upload_one_montg_form b =
  upd b (size 0) (u64 1);
  upd b (size 1) (u64 18446744069414584320);
  upd b (size 2) (u64 18446744073709551615);
  upd b (size 3) (u64 4294967294);

  assert_norm (1 + 18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 64 * pow2 64 + 4294967294 * pow2 64 * pow2 64 * pow2 64  == pow2 256 % prime256);
  lemmaToDomain 1


inline_for_extraction noextract
val montgomery_ladder_power_step0: a: felem -> b: felem -> Stack unit
  (requires fun h -> live h a /\ live h b /\ as_nat h a < prime /\
    as_nat h b < prime /\ disjoint a b )
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\
    as_nat h1 a < prime /\ as_nat h1 b < prime /\
    (
      let (r0D, r1D) = _pow_step0 (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b)) in
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b)
    )
)

let montgomery_ladder_power_step0 a b =
  let h0 = ST.get() in
    fmul a b b;
      lemmaToDomainAndBackIsTheSame (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 b) % prime);
    fsqr a a ;
      lemmaToDomainAndBackIsTheSame (fromDomain_ (as_nat h0 a) * fromDomain_ (as_nat h0 a) % prime)


inline_for_extraction noextract
val montgomery_ladder_power_step: a: felem -> b: felem -> scalar: glbuffer uint8 (size 32) ->   i:size_t{v i < 256} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar /\ as_nat h a < prime /\ as_nat h b < prime /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1  /\
    (
      let a_ = fromDomain_ (as_nat h0 a) in
      let b_ = fromDomain_ (as_nat h0 b) in
      let (r0D, r1D) = _pow_step (as_seq h0 scalar) (uint_v i) (a_, b_) in
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\
      as_nat h1 a < prime /\ as_nat h1 b < prime
    )
  )

let montgomery_ladder_power_step a b scalar i =
    let h0 = ST.get() in
  let bit0 = (size 255) -. i in
  let bit = scalar_bit scalar bit0 in
  cswap bit a b;
  montgomery_ladder_power_step0 a b;
  cswap bit a b;
  lemma_swaped_steps (fromDomain_ (as_nat h0 a)) (fromDomain_ (as_nat h0 b))


inline_for_extraction noextract
val _montgomery_ladder_power: a: felem -> b: felem -> scalar: glbuffer uint8 (size 32) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat h a < prime /\
    as_nat h b < prime /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\
    (
      let a_ = fromDomain_ (as_nat h0 a) in
      let b_ = fromDomain_ (as_nat h0 b) in
      let (r0D, r1D) = Lib.LoopCombinators.repeati 256 (_pow_step (as_seq h0 scalar)) (a_, b_) in
      r0D == fromDomain_ (as_nat h1 a) /\ r1D == fromDomain_ (as_nat h1 b) /\
      as_nat h1 a < prime /\ as_nat h1 b < prime)
  )


let _montgomery_ladder_power a b scalar =
  let h0 = ST.get() in
  [@inline_let]
  let spec_exp h0  = _pow_step (as_seq h0 scalar) in
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = (fromDomain_ (as_nat h a), fromDomain_ (as_nat h b)) in
  Lib.LoopCombinators.eq_repeati0 256 (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= 256}) =
    live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ as_nat h a < prime /\ as_nat h b < prime /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in
  Lib.Loops.for 0ul 256ul inv (
    fun i ->
	  montgomery_ladder_power_step a b scalar i;
	  Lib.LoopCombinators.unfold_repeati 256 (spec_exp h0) (acc h0) (uint_v i))


val montgomery_ladder_power: a: felem -> scalar: glbuffer uint8 (size 32) -> result: felem ->
  Stack unit
    (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat h a < prime /\ disjoint a scalar)
    (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
      as_nat h1 result < prime /\
      (
	assert_norm (1 < prime256);
	let r0D = pow_spec (as_seq h0 scalar) (fromDomain_ (as_nat h0 a)) in
	r0D == fromDomain_ (as_nat h1 result)
      )
    )


let montgomery_ladder_power a scalar result =
  assert_norm (1 < prime256);
  push_frame();
      let p = create (size 4) (u64 0) in
      upload_one_montg_form p;
      _montgomery_ladder_power p a scalar;
     lemmaToDomainAndBackIsTheSame 1;
    copy result p;
  pop_frame()


unfold let sqPower_list: list uint8 =
 [
   u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
   u8 0;  u8 0;  u8 0;  u8 64;  u8 0;   u8 0;   u8 0;   u8 0;
   u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 64;
   u8 0;  u8 0;  u8 0;  u8 192; u8 255; u8 255; u8 255; u8 63
 ]


let sqPower_seq: s: lseq uint8 32{Lib.ByteSequence.nat_from_intseq_le s == (prime256 + 1) / 4} =
  let open Lib.ByteSequence in
  assert_norm (List.Tot.length sqPower_list  == 32);
  nat_from_intlist_seq_le 32 sqPower_list;
  assert_norm (nat_from_intlist_le sqPower_list == (prime256 + 1) / 4);
  of_list sqPower_list


inline_for_extraction
let sqPower_buffer: x: glbuffer uint8 32ul {witnessed x sqPower_seq /\ recallable x} =
  createL_global sqPower_list


let square_root a result =
  recall_contents sqPower_buffer sqPower_seq;
  montgomery_ladder_power a sqPower_buffer result
