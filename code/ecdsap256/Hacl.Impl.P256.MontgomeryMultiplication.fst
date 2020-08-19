module Hacl.Impl.P256.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Impl.P256.Math 

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definition
open Hacl.Lemmas.P256
open Spec.P256
open Spec.ECDSA.Lemmas

open Hacl.Impl.P.LowLevel

open Lib.Loops
open Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 100"


inline_for_extraction noextract
val add_long_without_carry: #c: curve -> t: widefelem c -> t1: widefelem c -> result: widefelem c -> Stack unit
  (requires fun h -> 
    live h t /\ live h t1 /\ live h result /\ eq_or_disjoint t1 result /\ 
    eq_or_disjoint t result /\ 
    wide_as_nat c h t1 < getPower2 c * pow2 64 /\ 
    wide_as_nat c h t < getPrime c * getPrime c
  )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    wide_as_nat c h1 result = wide_as_nat c h0 t + wide_as_nat c h0 t1)


let add_long_without_carry #c t t1 result  = 
  let _  = add_long_bn t t1 result in 
    assert_norm (getPower2 P256 * pow2 64 + getPrime P256 * getPrime P256 < getLongPower2 P256);
    assert_norm (getPower2 P384 * pow2 64 + getPrime P384 * getPrime P384 < getLongPower2 P384)


val montgomery_multiplication_round: #c: curve -> t: widefelem c -> round: widefelem c -> 
  Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat c h t < getPrime c * getPrime c)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat c h1 round = (wide_as_nat c h0 t + getPrime c * (wide_as_nat c h0 t % pow2 64)) / pow2 64
  )


let montgomery_multiplication_round #c t round =
  push_frame(); 
    let h0 = ST.get() in 
    let len = getCoordinateLenU64 c in 
    
    let t2 = create (size 2 *! len) (u64 0) in 
    let t3 = create (size 2 *! len) (u64 0) in 
    let t1 = mod64 t in 
    
      recall_contents (prime_buffer #c) (Lib.Sequence.of_list (prime_list c)); 
    short_mul_bn (prime_buffer #c) t1 t2; 
    add_long_without_carry t t2 t3;
    shift1 t3 round; 
    admit();
  pop_frame()  


val montgomery_multiplication_one_round_proof: 
  #c: curve ->
  t: nat {t <  getPrime c * getPrime c} -> 
  result: nat {result = (t + (t % pow2 64) * getPrime c) / pow2 64} ->
  co: nat {co % getPrime c == t % getPrime c} -> 
  Lemma (
    result % getPrime c == co * modp_inv2 #c (pow2 64) % getPrime c /\
    result < getPrime c * getPrime c)


let montgomery_multiplication_one_round_proof t result co = 
  admit();
  mult_one_round t co;
  mul_lemma_1 (t % pow2 64) (pow2 64) prime256;
  assert_norm (prime256 * prime256 + pow2 64 * prime256 < pow2 575);
  lemma_div_lt (t + (t % pow2 64) * prime256) 575 64; 
  assert_norm (prime256 * prime256 > pow2 (575 - 64))


let montgomery_multiplication_buffer_by_one #c a result = 
  push_frame();
  
  let len = getCoordinateLenU64 c in 
  let t = create (size 2 *! len) (u64 0) in 
    let t_low = sub t (size 0) len in 
    let t_high = sub t len len in 
  copy t_low a; 

  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> montgomery_multiplication_round #c t t);

  reduction_prime_2prime_with_carry t result;
  pop_frame()  



let montgomery_multiplication_buffer #c a b result = 
  assert_norm(prime256 > 3);
  push_frame();
  let len = getCoordinateLenU64 c in 
  
  let round = create (size 2 *! len) (u64 0) in 
    let h0 = ST.get() in 
  mul a b round;  
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    True in 

  for 0ul len inv (fun i -> montgomery_multiplication_round #c round round);
      
  reduction_prime_2prime_with_carry round result; 
  pop_frame()  


let montgomery_square_buffer #c a result = 
  assert_norm(prime256 > 3);
  push_frame();
    
  let t = create (size 8) (u64 0) in 
    let h0 = ST.get() in 
  square_bn a t;  
    let h1 = ST.get() in 
    mul_lemma_ (as_nat P256 h0 a) (as_nat P256 h0 a) prime256;

  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = True in 
  for 0ul len inv (fun i -> montgomery_multiplication_round #c t t);

  reduction_prime_2prime_with_carry t result; 
   
  pop_frame()  



(* For p256 curve there is a special implementation of multiplication by prime - 2 *)
#reset-options "--z3rlimit 500" 

val fsquarePowN: n: size_t -> a: felem P256 -> Stack unit 
  (requires (fun h -> live h a /\ as_nat P256 h a < prime256)) 
  (ensures (fun h0 _ h1 -> 
    modifies (loc a) h0 h1 /\  as_nat P256 h1 a < prime256 /\ 
    (let k = fromDomain_ #P256 (as_nat P256 h0 a) in as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 (v n)))))
  )

let fsquarePowN n a = 
  let h0 = ST.get() in  
  lemmaFromDomainToDomain #P256 (as_nat P256 h0 a); 
  assert_norm (pow2 0 == 1); 
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k = fromDomain_ #P256 (as_nat P256 h0 a) in 
    as_nat P256 h1 a = toDomain_ #P256 (pow k (pow2 i)) /\
    as_nat P256 h1 a < prime256 /\ live h1 a /\ modifies1 a h0 h1  in 
  power_one (fromDomain_ #P256 (as_nat P256 h0 a)); 
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
    assert_norm(((pow2 32 - 1) * pow2 224 + pow2 192 + (pow2 94 -1 ) * pow2 2 + 1) = prime256 - 2)


[@ CInline]
val cswap: #c: curve ->  bit:uint64{v bit <= 1} -> p:felem c -> q:felem c
  -> Stack unit
    (requires fun h -> True)
    (ensures  fun h0 _ h1 ->
      modifies (loc p |+| loc q) h0 h1)


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
val montgomery_ladder_exponent_step0: #c: curve -> a: felem c-> b: felem c -> Stack unit
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 _ h1 -> True)

let montgomery_ladder_exponent_step0  #c a b = 
  montgomery_multiplication_buffer a b b;
  montgomery_multiplication_buffer a a a


inline_for_extraction noextract
val montgomery_ladder_exponent_step: #c: curve -> a: felem c -> b: felem c -> 
  scalar: glbuffer uint8 (getScalarLen c) ->   i:size_t{v i < getPower c} ->  Stack unit
  (requires fun h -> live h a  /\ live h b /\ live h scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1  )  

let montgomery_ladder_exponent_step #c a b scalar i = 
    let h0 = ST.get() in 
  let bit0 = (getPowerU c) -. 1 -. i in 
  let bit = Hacl.Impl.P256.LowLevel.scalar_bit scalar bit0 in 
  cswap bit a b;
  montgomery_ladder_exponent_step0 a b;
  cswap bit a b


inline_for_extraction noextract 
val _montgomery_ladder_exponent: #c: curve -> a: felem c ->b: felem c ->  
  scalar: glbuffer uint8 (getScalarLen c) -> Stack unit
  (requires fun h -> live h a /\ live h b /\ live h scalar /\ disjoint a b /\disjoint a scalar /\ disjoint b scalar)
  (ensures fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1)

  
let _montgomery_ladder_exponent #c a b scalar = 
  let h0 = ST.get() in 
  let len = getPowerU c in 
(*  [@inline_let]
  let spec_exp h0  = _exp_step #P256 (as_seq h0 scalar) in  
  [@inline_let]
  let acc (h: mem) : GTot (tuple2 nat_prime nat_prime) = (fromDomain_ (as_nat c h a), fromDomain_ (as_nat c h b)) in 
  Lib.LoopCombinators.eq_repeati0 256 (spec_exp h0) (acc h0); *)
  [@inline_let]
  let inv h (i: nat {i <= getPower c}) = 
    live h a /\ live h b /\ live h scalar
    (*modifies (loc a |+| loc b) h0 h /\ as_nat c h a < prime /\ as_nat c h b < prime /\
    acc h == Lib.LoopCombinators.repeati i (spec_exp h0) (acc h0) *) in 
  for 0ul len inv (
    fun i -> 
	  montgomery_ladder_exponent_step a b scalar i (*;
	  Lib.LoopCombinators.unfold_repeati 256 (spec_exp h0) (acc h0) (uint_v i) *) )


(* and the others *)
val _exponent: #c: curve -> a: felem c -> result: felem c 
  -> tempBuffer: lbuffer uint64 (size 5 *! getCoordinateLenU64 c) 
  -> Stack unit
    (requires fun h -> 
      live h a /\ live h tempBuffer /\ live h result /\  disjoint tempBuffer result /\ 
      disjoint a tempBuffer /\ as_nat c h a < getPrime c)
    (ensures fun h0 _ h1 -> 
      modifies2 result tempBuffer h0 h1 /\
      (let k = fromDomain_ #c (as_nat c h0 a) in 
      as_nat c h1 result =  toDomain_ #c (pow k (getPrime c - 2) % getPrime c)))

let _exponent #c r result tempBuffer = 
  let len = getCoordinateLenU64 c in 
  let p = sub tempBuffer (size 0) len in 
  upload_one_montg_form #c p; 
  _montgomery_ladder_exponent p r prime_inverse_buffer;
  copy result p;
  pop_frame()  


#reset-options " --z3rlimit 200"
let exponent #c a result tempBuffer = 
  match c with 
  |P384 -> _exponent #P384 a result tempBuffer
  |P256 -> exponent_p256 a result tempBuffer

