module Hacl.Impl.P256.MM.Exponent

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas

open Hacl.Impl.P.LowLevel 

open FStar.Mul

open Lib.Loops

open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.ECDSA.Lemmas
open Spec.P256
open Hacl.Spec.P256.MontgomeryMultiplication

friend Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(* For p256 curve there is a special implementation of multiplication by prime - 2 *)

val fsquarePowN: n: size_t -> a: felem P256 -> Stack unit 
  (requires (fun h -> live h a /\ as_nat P256 h a < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc a) h0 h1 /\  as_nat P256 h1 a < prime256 /\ 
    (let k = fromDomain_ #P256 (as_nat P256 h0 a) in as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 (v n))))))

let fsquarePowN n a = 
  let h0 = ST.get() in  
  lemmaFromDomainToDomain #P256 (as_nat P256 h0 a); 
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 i)) /\
    as_nat P256 h1 a < prime256 /\ live h1 a /\ modifies1 a h0 h1  in 
  
  power_one (fromDomain_ #P256 (as_nat P256 h0 a)); 
  admit();
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_square_buffer a a; 
     let k = fromDomain_ #P256 (as_nat P256 h0 a) in  
     inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0_ a) * fromDomain_ #P256 (as_nat P256 h0_ a)); 
     lemmaFromDomainToDomainModuloPrime #P256 (let k = fromDomain_ #P256 (as_nat P256 h0 a) in pow k (pow2 (v x)));
     modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256; 
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x);
     inDomain_mod_is_not_mod #P256 (pow k (pow2 (v x + 1)))
  )


val fsquarePowNminusOne: n: size_t -> a: felem P256 -> tempBuffer: felem P256 -> Stack unit 
  (requires (fun h -> live h a /\ live h tempBuffer /\ as_nat P256 h a < prime256 /\ disjoint a tempBuffer)) 
  (ensures (fun h0 _ h1 -> 
    as_nat P256 h1 a < prime256 /\ as_nat P256 h1 tempBuffer < prime256 /\ 
    modifies (loc a |+| loc tempBuffer) h0 h1 /\ 
    (
      let k = fromDomain_ #P256 (as_nat P256 h0 a) in  
      as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 (v n))) /\ as_nat P256 h1 tempBuffer = 
	toDomain_ #P256 (pow k (pow2 (v n) -1 )))
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
      lemmaFromDomainToDomain #P256 (as_nat P256 h0 a);
      lemmaToDomain #P256 1;
      assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 = 26959946660873538059280334323183841250350249843923952699046031785985);
      assert_norm (pow2 256 % prime256 == 26959946660873538059280334323183841250350249843923952699046031785985);
      assert_norm (as_nat_coordinate #P256 one = toDomain_ #P256 1);

  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = 
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 b = toDomain_ #P256 (pow k (pow2 i - 1)) /\ as_nat  P256 h1 a < prime256 /\ live h1 a /\
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 i)) /\ as_nat P256 h1 b < prime256 /\ live h1 b /\ modifies (loc a |+| loc b) h0 h1 in 
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
    montgomery_multiplication_buffer b a b;
    montgomery_square_buffer a a;
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0_ b) * fromDomain_ #P256 (as_nat P256 h0_ a));
    inDomain_mod_is_not_mod #P256 (fromDomain_ #P256 (as_nat P256 h0_ a) * fromDomain_ #P256 (as_nat P256 h0_ a));

    lemmaFromDomainToDomainModuloPrime #P256 (pow k (pow2 (v x) - 1));
    lemmaFromDomainToDomainModuloPrime #P256 (pow k (pow2 (v x)));
    modulo_distributivity_mult (pow k (pow2 (v x) - 1)) (pow k (pow2 (v x))) prime256;
    modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime256;
    
    pow_plus k (pow2 (v x) -1 ) (pow2 (v x));
    pow_plus k (pow2 (v x)) (pow2 (v x));
    pow2_double_sum (v x);

    inDomain_mod_is_not_mod #P256 (pow k (pow2 (v x + 1)));
    inDomain_mod_is_not_mod #P256 (pow k (pow2 (v x + 1) - 1))
)


inline_for_extraction noextract   
val norm_part_one: a: felem P256 -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat P256 h a < prime256)
  (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat P256 h1 buffer_result < prime256 /\ 
  (let k = fromDomain_ #P256 (as_nat P256 h0 a) in as_nat P256 h1 buffer_result = toDomain_ #P256 (pow k ((pow2 32 - 1) * pow2 224) % prime256))))
    
let norm_part_one a tempBuffer = 
    let h0 = ST.get() in 
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in 
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 

  fsquarePowNminusOne (size 32) buffer_a buffer_b;
  fsquarePowN (size 224) buffer_b;

  let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
  lemmaFromDomainToDomainModuloPrime #P256 (pow k (pow2 32 - 1));
  let k_powers = pow k (pow2 32 - 1) in 
  let k_prime = k_powers % prime256 in 
  inDomain_mod_is_not_mod #P256 (pow k_prime (pow2 224));
  power_distributivity k_powers (pow2 224) prime256;
  power_mult k (pow2 32 - 1) (pow2 224)
 
 
inline_for_extraction noextract   
val norm_part_two: a: felem P256 -> tempBuffer: lbuffer uint64 (size 4) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat P256 h a < prime256)
  (ensures fun h0 _ h1 -> as_nat P256 h1 tempBuffer < prime256 /\ modifies1 tempBuffer h0 h1 /\
    (let k = fromDomain_ #P256 (as_nat P256 h0 a) in as_nat P256 h1 tempBuffer = toDomain_ #P256 (pow k (pow2 192) % prime256)))
    
let norm_part_two a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.copy tempBuffer a;
  fsquarePowN (size 192) tempBuffer;
  let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
  inDomain_mod_is_not_mod #P256 (pow k (pow2 192))


inline_for_extraction noextract   
val norm_part_three:a: felem P256 -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  
   as_nat P256 h a < prime256)   
  (ensures fun h0 _ h1 ->  modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat P256 h1 buffer_result < prime256
    /\ (let k = fromDomain_ #P256 (as_nat P256 h0 a) in as_nat P256 h1 buffer_result = toDomain_ #P256 (pow k ((pow2 94 - 1) * pow2 2) % prime256))))

let norm_part_three a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in 
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 

  fsquarePowNminusOne (size 94) buffer_a buffer_b;
  fsquarePowN (size 2) buffer_b;

  let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
  lemmaFromDomainToDomainModuloPrime #P256 (pow k (pow2 94 - 1));
  let k_powers = pow k (pow2 94 - 1) in 
  let k_prime = k_powers % prime256 in 
  inDomain_mod_is_not_mod #P256 (pow k_prime (pow2 2));
  power_distributivity k_powers (pow2 2) prime256;
  power_mult k (pow2 94 - 1) (pow2 2)


val lemma_inDomainModulo: a: nat -> b: nat -> Lemma ((toDomain_ #P256 ((a % prime256) * (b % prime256) % prime256) = toDomain_ #P256 (a * b % prime256)))

let lemma_inDomainModulo a b = 
  lemma_mod_mul_distr_l a (b % prime256) prime256;
  lemma_mod_mul_distr_r a b prime256


let lemmaEraseToDomainFromDomain z = 
  lemma_mod_mul_distr_l (z * z) z prime256


val big_power: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (pow a b * pow a c * pow a d * pow a e = pow a (b + c + d + e))

let big_power a b c d e = 
  assert(pow a b * pow a c * pow a d * pow a e = (pow a b * pow a c) * (pow a d * pow a e));
  pow_plus a b c;
  pow_plus a d e;
  pow_plus a (b + c) (d + e)

val lemma_mul_nat: a: nat -> b: nat -> Lemma (a * b >= 0)

let lemma_mul_nat a b = ()



val exponent_p256: a: felem P256-> result: felem P256-> tempBuffer: lbuffer uint64 (size 20) ->  Stack unit
  (requires fun h -> live h a /\ live h tempBuffer /\ live h result /\ disjoint tempBuffer result /\ 
  disjoint a tempBuffer /\ as_nat P256 h a < prime256)
  (ensures fun h0 _ h1 -> modifies2 result tempBuffer h0 h1 /\ (let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 result =  toDomain_ #P256 ((pow k (prime256 - 2)) % prime256)))

let exponent_p256 a result tempBuffer =    
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
    montgomery_multiplication_buffer #P256 buffer_result1 buffer_result2 buffer_result1;
      let h2 = ST.get() in 
    montgomery_multiplication_buffer #P256 buffer_result1 buffer_result3 buffer_result1;
      let h3 = ST.get() in 
    montgomery_multiplication_buffer #P256 buffer_result1 a buffer_result1;
      let h4 = ST.get() in 
    copy result buffer_result1; 
      let h5 = ST.get() in 
    assert_norm ((pow2 32 - 1) * pow2 224 >= 0);
    assert_norm (pow2 192 >= 0);
    assert_norm ((pow2 94 - 1) * pow2 2 >= 0);

    
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    let power1 = pow k ((pow2 32 - 1) * pow2 224) in 
    let power2 = pow k (pow2 192) in 
    let power3 = pow k ((pow2 94 - 1) * pow2 2) in 
    let power4 = pow k 1 in 

    lemma_mul_nat power1 power2;

    lemma_inDomainModulo power1 power2;
    lemma_inDomainModulo (power1 * power2) power3;
    inDomain_mod_is_not_mod #P256 (((power1 * power2 * power3) % prime256 * power4));
    lemma_mod_mul_distr_l (power1 * power2 * power3) power4 prime256;
    big_power k ((pow2 32 - 1) * pow2 224) (pow2 192) ((pow2 94 -1 ) * pow2 2) 1;
    assert_norm(((pow2 32 - 1) * pow2 224 + pow2 192 + (pow2 94 -1 ) * pow2 2 + 1) = prime256 - 2);
    admit()



[@ CInline]
val cswap: #c: curve -> bit:uint64{v bit <= 1} -> p: felem c -> q: felem c
  -> Stack unit
    (requires fun h ->  as_nat c h p < getPrime c /\ as_nat c h q < getPrime c /\ 
      live h p /\ live h q /\ eq_or_disjoint p q)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1 /\
	(
	  let (r0, r1) = conditional_swap_pow #c bit (as_nat c h0 p) (as_nat c h0 q) in 
	  let pBefore = as_seq h0 p in let qBefore = as_seq h0 q in 
	  let pAfter = as_seq h1 p in let qAfter = as_seq h1 q in 
	  as_nat c h1 p < getPrime c /\ as_nat c h1 q < getPrime c /\
      (v bit == 1 ==> as_seq h1 p == as_seq h0 q /\ as_seq h1 q == as_seq h0 p) /\
      (v bit == 0 ==> as_seq h1 p == as_seq h0 p /\ as_seq h1 q == as_seq h0 q)))


let cswap #c bit p1 p2 =
  
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  let len = getCoordinateLenU64 c in 

  let open Lib.Sequence in 
  [@ inline_let]
  let inv h1 (i:nat{i <= uint_v len}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 4}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul len inv
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
val montgomery_ladder_power_step0: #c: curve -> a: felem c -> b: felem c -> Stack unit
  (requires fun h -> live h a /\ live h b /\ as_nat c h a < getPrime c /\ 
    as_nat c h b < getPrime c /\ disjoint a b )
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c /\
    (
      let (r0D, r1D) = _pow_step0 #c (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 b)) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b)
    )
)

let montgomery_ladder_power_step0 #c a b = 
  let h0 = ST.get() in 
    montgomery_multiplication_buffer a b b;
      lemmaToDomainAndBackIsTheSame #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 b) % getPrime c);
    montgomery_square_buffer a a ;
      lemmaToDomainAndBackIsTheSame #c (fromDomain_ #c (as_nat c h0 a) * fromDomain_ #c (as_nat c h0 a) % getPrime c)


inline_for_extraction noextract
val montgomery_ladder_power_step: #c: curve -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getScalarLen c) 
  -> i:size_t{v i < getScalarLenNat c} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar /\ as_nat c h a < getPrime c 
    /\ as_nat c h b < getPrime c /\ disjoint a b)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1  /\
    (
      let a_ = fromDomain_ #c (as_nat c h0 a) in 
      let b_ = fromDomain_ #c (as_nat c h0 b) in 
      let (r0D, r1D) = _pow_step #c (as_seq h0 scalar) (uint_v i) (a_, b_) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b) /\ 
      as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c 
    ) 
  )  

let montgomery_ladder_power_step #c a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = getScalarLen c -. 1ul -. i in 
  let bit = scalar_bit scalar bit0 in 
  cswap bit a b;
  montgomery_ladder_power_step0 a b;
  cswap bit a b;
  lemma_swaped_steps #c (fromDomain_ #c (as_nat c h0 a)) (fromDomain_ #c (as_nat c h0 b))


val _montgomery_ladder_power: #c: curve -> a: felem c -> b: felem c 
  -> scalar: glbuffer uint8 (getScalarLen c) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ as_nat c h a < getPrime c /\ 
    as_nat c h b < getPrime c /\ disjoint a b /\ disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\ 
    (
      let a_ = fromDomain_ #c (as_nat c h0 a) in 
      let b_ = fromDomain_ #c (as_nat c h0 b) in 
      let (r0D, r1D) = Lib.LoopCombinators.repeati (getScalarLenNat c) (_pow_step #c (as_seq h0 scalar)) (a_, b_) in 
      r0D == fromDomain_ #c (as_nat c h1 a) /\ r1D == fromDomain_ #c (as_nat c h1 b) /\
      as_nat c h1 a < getPrime c /\ as_nat c h1 b < getPrime c)
  )

  
let _montgomery_ladder_power #c a b scalar = 
  let scalarLen = getScalarLen c in 
  let h0 = ST.get() in 
  [@inline_let]
  let spec_exp h0  = _pow_step #c (as_seq h0 scalar) in 
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = (fromDomain_ #c (as_nat c h a), fromDomain_ #c (as_nat c h b)) in 
  Lib.LoopCombinators.eq_repeati0 (getScalarLenNat c) (spec_exp h0) (acc h0);
  [@inline_let]
  let inv h (i: nat {i <= (getScalarLenNat c)}) = 
    live h a /\ live h b /\ live h scalar /\ modifies (loc a |+| loc b) h0 h /\ as_nat c h a < getPrime c /\ as_nat c h b < getPrime c /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) in 
  for 0ul scalarLen inv (
    fun i -> 
	  montgomery_ladder_power_step a b scalar i;
	  Lib.LoopCombinators.unfold_repeati (getScalarLenNat c) (spec_exp h0) (acc h0) (uint_v i))


val montgomery_ladder_power: #c: curve -> a: felem c 
  -> scalar: glbuffer uint8 (getScalarLen c) -> result: felem c -> 
  Stack unit 
    (requires fun h -> live h a /\ live h scalar /\ live h result /\ as_nat c h a < getPrime c /\ disjoint a scalar)
    (ensures fun h0 _ h1 -> modifies (loc a |+| loc result) h0 h1 /\
      as_nat c h1 result < getPrime c /\ 
      (
	let r0D = pow_spec #c (as_seq h0 scalar) (fromDomain_ #c (as_nat c h0 a)) in 
	r0D == fromDomain_ #c (as_nat c h1 result)
      ) 
    )


let montgomery_ladder_power #c a scalar result = 
  assert_norm (1 < prime256);
  push_frame(); 
  let sz = getCoordinateLenU64 c in 
  let p = create sz (u64 0) in  
    upload_one_montg_form #c p; 
      _montgomery_ladder_power #c p a scalar;
     lemmaToDomainAndBackIsTheSame #c 1;  
    copy result p;
    admit(); 
  pop_frame()  


#reset-options " --z3rlimit 200"
let exponent #c a result tempBuffer = 
  match c with 
  |P384 -> montgomery_ladder_power #c a prime_inverse_buffer result
  |P256 -> exponent_p256 a result tempBuffer



unfold let sqPower_list (#c: curve) : list uint8 =
  match c with 
  |P256 -> 
    [
      u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;  u8 0;  u8 0;  u8 64;  u8 0;   u8 0;   u8 0;   u8 0;
      u8 0;  u8 0;  u8 0;  u8 0;   u8 0;   u8 0;   u8 0;   u8 64;
      u8 0;  u8 0;  u8 0;  u8 192; u8 255; u8 255; u8 255; u8 63
    ]
  |P384 -> 
    [
      u8 255; u8 255; u8 255; u8 63;  u8 0;   u8 0;   u8 0;   u8 0;
      u8 0  ; u8 0  ; u8 0;   u8 192; u8 255; u8 255; u8 255; u8 191;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
      u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 63    
    ]


let sqPower_seq (#c: curve) : s: lseq uint8 (getScalarLenNat c)
  {Lib.ByteSequence.nat_from_intseq_le s == 
  (getPrime c + 1) / 4} =
  let open Lib.ByteSequence in 
  assert_norm (List.Tot.length (sqPower_list #P256) == 32);
  assert_norm (List.Tot.length (sqPower_list #P384) == 48);
  
  nat_from_intlist_seq_le 32 (sqPower_list #P256);
  nat_from_intlist_seq_le 48 (sqPower_list #P384);
  
  assert_norm (nat_from_intlist_le (sqPower_list #P256)  == (getPrime P256 + 1) / 4);
  assert_norm (nat_from_intlist_le (sqPower_list #P384)  == (getPrime P384 + 1) / 4);
  of_list (sqPower_list #c)




inline_for_extraction
let sqPower_buffer_p256 : x: glbuffer uint8 (getScalarLen P256) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global (sqPower_list #P256)

inline_for_extraction
let sqPower_buffer_p384 : x: glbuffer uint8 (getScalarLen P384) {witnessed x sqPower_seq /\ recallable x} = 
  createL_global (sqPower_list #P384)

inline_for_extraction
let sqPower_buffer (#c: curve): (x: glbuffer uint8 (getScalarLen c)) = 
  match c with
  |P256 -> sqPower_buffer_p256 
  |P384 -> sqPower_buffer_p384 


let square_root #c a result = 
  recall_contents sqPower_buffer (sqPower_seq #c);
  montgomery_ladder_power a sqPower_buffer result
