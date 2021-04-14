module Hacl.Impl.ECDSA.Signature

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECDSA
open Hacl.Lemmas.P256

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Hash.SHA2
open Hacl.Spec.EC.Definition

open Spec.ECC
open Spec.ECC.Curves
(* open Spec.ECC.Lemmas *)
open Hacl.Spec.EC.Definition
open Hacl.Spec.ECDSA.Definition

open Hacl.Spec.ECDSA.Definition

open Hacl.Impl.EC.LowLevel 

open Hacl.Impl.EC.Core

open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.LowLevel

open Hacl.Impl.P256.Signature.Common

module H = Spec.Agile.Hash
module Def = Spec.Hash.Definitions

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open Hacl.Impl.EC.Intro
open Hacl.Impl.EC.Masking

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.MontgomeryMultiplication


#set-options "--z3rlimit 100 --ifuel 0 --fuel 0"

let prime_p256_order #c = getOrder #c

val ecdsa_signature_step12: 
  #c: curve 
  -> alg:hash_alg_ecdsa
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen -> result: felem c -> Stack unit
  (requires fun h -> live h m /\ live h result )
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 (*/\
    (
      assert_norm (pow2 32 < pow2 61);
      assert_norm (pow2 32 < pow2 125);
      let hashM = hashSpec P256 alg (v mLen) (as_seq h0 m) in 
      let cutHashM = Lib.Sequence.sub hashM 0 32 in 
      as_nat c h1 result = nat_from_bytes_be cutHashM % prime_p256_order
    ) *)
  )


let ecdsa_signature_step12 #c alg mLen m result = 
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame(); 
    let h0 = ST.get() in 
  let sz_hash: FStar.UInt32.t = match alg with |NoHash -> mLen |Hash a -> hash_len a in
    assume (v sz_hash + v (getCoordinateLenU c) < pow2 32);
  let len: FStar.UInt32.t  = getCoordinateLenU c in 
  let mHash = create (sz_hash +! len) (u8 0) in 
    let mHashHPart = sub mHash (size 0) sz_hash in 
    let mHashRPart = sub mHash (size 0) (getCoordinateLenU c) in 
  begin
  match alg with 
    |NoHash -> copy mHashHPart m 
    |Hash a -> match a with 
      |SHA2_256 -> hash_256 m mLen mHashHPart
      |SHA2_384 -> hash_384 m mLen mHashHPart
      |SHA2_512 -> hash_512 m mLen mHashHPart 
  end;

  toUint64ChangeEndian #c mHashRPart result;
  reduction_prime_2prime_order result result;

  let h1 = ST.get() in 

  lemma_core_0 c result h1;
  admit();
  (* changeEndianLemma #c (uints_from_bytes_be #U64 #_ #_ (as_seq h1 mHashRPart));  *)
  uints_from_bytes_be_nat_lemma #U64 #_ #(v (getCoordinateLenU64 c)) (as_seq h1 mHashRPart); 
  pop_frame()



#push-options "--ifuel 1"

val ecdsa_signature_step45:
  c: curve
  -> x: felem c
  -> k: lbuffer uint8 (getScalarLenBytes c) 
  -> tempBuffer: lbuffer uint64 (size 100) -> 
  Stack uint64
  (requires fun h -> live h x /\ live h k /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc k; loc x])
  (ensures fun h0 r h1 -> modifies (loc x |+| loc tempBuffer) h0 h1 /\ 
    as_nat c h1 x < getOrder #c /\ (
    let (rxN, ryN, rzN), _ = montgomery_ladder_spec_left #c (as_seq h0 k) ((0,0,0), basePoint #c) in 
    let (xN, _, _) = _norm #c (rxN, ryN, rzN) in 
    as_nat c h1 x == xN % getOrder #c /\ (
    if as_nat c h1 x = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0)))

let ecdsa_signature_step45 c x k tempBuffer = 
  push_frame();
    let result = create (size 12) (u64 0) in 
    let tempForNorm = sub tempBuffer (size 0) (size 88) in 
    secretToPublicWithoutNorm #c result k tempBuffer; 
    normX #c result x tempForNorm;
    reduction_prime_2prime_order x x;
  pop_frame();
    isZero_uint64_CT #c x

#pop-options

val lemma_power_step6: #c: curve -> kInv: nat -> Lemma 
  (Spec.ECDSA.exponent_spec #c (fromDomain_ #c #DSA kInv) == toDomain_ #c #DSA (pow kInv (getOrder #c - 2)))

let lemma_power_step6 #c kInv = 
  let a = Spec.ECDSA.exponent_spec #c (fromDomain_ #c #DSA kInv) in 
  let order = getOrder #c in 
  lemmaFromDomain #c #DSA kInv (*

  power_distributivity (kInv * modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2) prime_p256_order;
  power_distributivity_2 kInv (modp_inv2_prime (pow2 256) prime_p256_order % prime_p256_order) (prime_p256_order - 2);
  lemma_mod_mul_distr_r (pow kInv (prime_p256_order - 2)) (pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2)) prime_p256_order;

  lemma_pow_mod_n_is_fpow prime_p256_order (pow2 256 % prime_p256_order) (prime_p256_order - 2);
  
  let inverse2_256 = 43790243014242295660885426880012836369732278457577312309071968676491870960761 in 
  assert_norm(modp_inv2_prime (pow2 256) prime_p256_order = inverse2_256); 
  lemma_pow_mod_n_is_fpow prime_p256_order inverse2_256 (prime_p256_order - 2);
  assert_norm(exp #prime_p256_order inverse2_256 (order - 2) == pow2 256 % order);

  lemma_mod_mul_distr_r (pow kInv (order - 2)) (pow2 256) order;
  lemmaToDomain (pow kInv (getOrder #c - 2)) *)


val ecdsa_signature_step6: #c: curve -> result: felem c
  -> kFelem: felem c
  -> z: felem  c
  -> r: felem c
  -> da: felem  c
  -> Stack unit
    (requires fun h ->  True (*
      live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\
      as_nat c h kFelem < prime_p256_order /\ 
      as_nat c h z < prime_p256_order /\ 
      as_nat c h r < prime_p256_order /\ 
      as_nat c h da < prime_p256_order *)
    )
    (ensures fun h0 _ h1 -> 
      modifies (loc result) h0 h1  (*/\
      as_nat c h1 result = (as_nat c h0 z + as_nat c h0 r * as_nat c h0 da) * pow (as_nat c h0 kFelem) (prime_p256_order - 2) % prime_p256_order *)
    ) 

open Hacl.Impl.MM.Exponent

let ecdsa_signature_step6 #c result kFelem z r da = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  push_frame();
    let len : FStar.UInt32.t  = getCoordinateLenU64 c in 
    let rda = create len (u64 0) in 
    let zBuffer = create len (u64 0) in 
    let kInv = create len (u64 0) in 
  let h0 = ST.get() in 
    montgomery_multiplication_buffer_dsa #c r da rda;
    fromDomainImpl z zBuffer;
    felem_add #c rda zBuffer zBuffer;  
    copy kInv kFelem; (*
    montgomery_ladder_power #c #DSA kInv; *)
    montgomery_multiplication_buffer_dsa zBuffer kInv result;
  pop_frame()
      (*let br0 = as_nat c h0 z + as_nat c h0 r * as_nat c h0 da in
      let br1 = pow (as_nat c h0 kFelem) (prime_p256_order - 2) in 

      lemmaFromDomain (as_nat c h0 r * as_nat c h0 da); 
      lemma_felem_add (as_nat c h0 r * as_nat c h0 da) (as_nat c h0 z);
      lemma_power_step6 (as_nat c h0 kFelem); 

      lemmaFromDomain (fromDomain_ br0);
      lemmaToDomain br1;
      assert_norm ((modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) % prime_p256_order = 1);
       
      lemma_mod_mul_distr_l (fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order) (br1 * pow2 256 % prime_p256_order) prime_p256_order;
      lemma_mod_mul_distr_r (fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order) (br1 * pow2 256) prime_p256_order;
       
      assert_by_tactic (fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order * (br1 * pow2 256) == fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1 * pow2 256) canon;
      assert_by_tactic (fromDomain_ br0 * br1 * (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) == fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1 * pow2 256) canon;
       
      lemma_mod_mul_distr_r (fromDomain_ br0 * br1) (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) prime_p256_order;
      lemmaToDomain ((fromDomain_ br0 * br1) % prime_p256_order);
      lemmaFromDomain br0;
       
      lemma_mod_mul_distr_l (br0 * modp_inv2_prime (pow2 256) prime_p256_order) br1 prime_p256_order;
      lemma_mod_mul_distr_l (br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1) (pow2 256) prime_p256_order;
       
      assert_by_tactic (br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1 * pow2 256 = br0 * br1 * (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256)) canon;
      lemma_mod_mul_distr_r (br0 * br1) (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) prime_p256_order;
      lemma_mod_mul_distr_r br0 br1 prime_p256_order *) 

#push-options "--ifuel 1"

val ecdsa_signature_core: #c: curve -> alg: hash_alg_ecdsa
  -> r: felem  c
  -> s: felem c
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #P256 alg}
  -> m: lbuffer uint8 mLen 
  -> privKeyAsFelem: felem  c
  -> k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h r /\ live h s /\ live h m /\ live h privKeyAsFelem /\ live h k /\
    disjoint privKeyAsFelem r /\
    disjoint privKeyAsFelem s /\
    disjoint k r /\
    disjoint r s /\   
    as_nat c h privKeyAsFelem < getOrder #c /\
    as_nat c h s == 0 /\
    nat_from_bytes_be (as_seq h k) < getOrder #c
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc r |+| loc s) h0 h1 (* /\
    (
      assert_norm (pow2 32 < pow2 61); 
      assert_norm (pow2 32 < pow2 125);
      let hashM = hashSpec P256 alg (v mLen) (as_seq h0 m) in 
      let cutHashM = Lib.Sequence.sub hashM 0 32 in 
      let z =  nat_from_bytes_be cutHashM % prime_p256_order in 
      let (rxN, ryN, rzN), _ = montgomery_ladder_spec_left #c (as_seq h0 k) ((0,0,0), basePoint #P256) in 
      let (xN, _, _) = _norm #P256 (rxN, ryN, rzN) in 
      
      let kFelem = nat_from_bytes_be (as_seq h0 k) in 
      as_nat c h1 r == xN % prime_p256_order /\
      as_nat c h1 s == (z + (as_nat c h1 r) * as_nat c h0 privKeyAsFelem) * pow kFelem (prime_p256_order - 2) % prime_p256_order /\
      (
	if as_nat c h1 r = 0 || as_nat c h1 s = 0 then 
	  uint_v flag == pow2 64 - 1
	else 
	  uint_v flag == 0
      )
    ) *)
  )


let ecdsa_signature_core #c alg r s mLen m privKeyAsFelem k = 
  push_frame();
  let h0 = ST.get() in 
    let sz: FStar.UInt32.t = getCoordinateLenU64 c in 
  let hashAsFelem = create sz (u64 0) in     
  let tempBuffer = create (size 100) (u64 0) in 
  let kAsFelem = create sz (u64 0) in 
  toUint64ChangeEndian #c k kAsFelem;
  ecdsa_signature_step12 #c alg mLen m hashAsFelem;
  let h1 = ST.get() in 
  lemma_core_0 c kAsFelem h1;
  (* changeEndianLemma #c (uints_from_bytes_be (as_seq h0 k)); *)
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 k);
  let step5Flag = ecdsa_signature_step45 c r k tempBuffer in 
  assert_norm (pow2 32 < pow2 61);
  ecdsa_signature_step6 #c s kAsFelem hashAsFelem r privKeyAsFelem;  
  let sIsZero = isZero_uint64_CT #c s in 
  logor_lemma step5Flag sIsZero;
  pop_frame(); 
  admit(); 
  logor step5Flag sIsZero



#pop-options

inline_for_extraction noextract
val ecdsa_signature: 
  c: curve 
  -> alg: hash_alg_ecdsa 
  -> result: lbuffer uint8 (size 64) 
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #P256 alg}
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k (*
    nat_from_bytes_be (as_seq h privKey) < prime_p256_order /\
    nat_from_bytes_be (as_seq h k) < prime_p256_order *)
  )
  (ensures fun h0 flag h1 -> 
    modifies (loc result) h0 h1 /\
     (assert_norm (pow2 32 < pow2 61);
      let resultR = gsub result (size 0) (size 32) in 
      let resultS = gsub result (size 32) (size 32) in 
      let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile P256 alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
      as_seq h1 resultR == nat_to_bytes_be 32 r /\
      as_seq h1 resultS == nat_to_bytes_be 32 s /\
      flag == flagSpec 
    )    
  )


let ecdsa_signature c alg result mLen m privKey k = 
  push_frame();
  let h0 = ST.get() in 
  assert_norm (pow2 32 < pow2 61); 
  let privKeyAsFelem = create (size 4) (u64 0) in 
  let r = create (size 4) (u64 0) in 
  let s = create (size 4) (u64 0) in 
  let resultR = sub result (size 0) (size 32) in 
  let resultS = sub result (size 32) (size 32) in 
  toUint64ChangeEndian #c privKey privKeyAsFelem;

  let h1 = ST.get() in 
  lemma_core_0 privKeyAsFelem c h1;
  (* changeEndianLemma #c (uints_from_bytes_be (as_seq h0 privKey)); *)
  uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h1 privKey);    
  let flag = ecdsa_signature_core #c alg r s mLen m privKeyAsFelem k in 

  let h2 = ST.get() in 
  
  changeEndian #c r;
  toUint8 #c r resultR;
  lemma_core_0 c r h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 r);

  changeEndian #c s;
  toUint8 #c s resultS;
  let h3 = ST.get() in 
  lemma_core_0 c s h2;
  lemma_nat_from_to_intseq_le_preserves_value 4 (as_seq h2 s);

  (* changeEndian_le_be #c (as_nat c h2 r);
  changeEndian_le_be #c (as_nat c h2 s); *)

  pop_frame();
  flag  
