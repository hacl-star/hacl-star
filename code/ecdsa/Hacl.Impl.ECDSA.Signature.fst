module Hacl.Impl.ECDSA.Signature

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECDSA
open Hacl.EC.Lemmas

open FStar.Mul
open FStar.Math.Lemmas

open Hacl.Hash.SHA2

open Spec.ECC
open Spec.ECC.Curves
open Hacl.Spec.EC.Definition

open Hacl.Impl.EC.Core
open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.ECDSA.LowLevel

open Hacl.Impl.P256.Signature.Common
open Spec.Hash.Definitions
open Hacl.Hash.Definitions

open Hacl.Impl.EC.Intro
open Hacl.Impl.EC.Masking

open Hacl.Impl.EC.MontgomeryMultiplication
open Hacl.Spec.MontgomeryMultiplication



#set-options "--z3rlimit 200 --max_ifuel 0 --max_fuel 0"

(* 
Let {\displaystyle z}z be the {\displaystyle L_{n}}L_{n} leftmost bits of {\displaystyle e}e, where {\displaystyle L_{n}}L_{n} is the bit length of the group order {\displaystyle n}n. (Note that {\displaystyle z}z can be greater than {\displaystyle n}n but not longer.[2])
*)
inline_for_extraction
val ecdsa_signature_step12: 
  #c: curve 
  -> alg:hash_alg_ecdsa
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg} 
  -> m: lbuffer uint8 mLen -> result: felem c -> Stack unit
  (requires fun h -> live h m /\ live h result /\ 
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (
    let message = hashSpec c alg (v mLen) (as_seq h0 m) in 
    as_nat c h1 result == message % getOrder #c /\
    as_nat c h1 result < getOrder #c))


val ecdsa_signature_step12_lemma: cur: curve -> l: size_t{v l > 0} -> l1: size_t {v l + v l1 < pow2 32 /\ v l1 > 0} 
  -> h0: mem -> h1: mem -> 
  mHash: lbuffer uint8 (l +! l1) {lseq_as_nat (as_seq h0 mHash) == 0 /\ live h0 mHash} -> 
  mHashHPart: lbuffer uint8 l {mHashHPart == gsub mHash (size 0) l /\ modifies (loc mHashHPart) h0 h1} ->
  hashS: Lib.Sequence.lseq uint8 (v l) {as_seq h1 mHashHPart == hashS} -> Lemma (
    let mHashRPart = gsub mHash (size 0) l1 in 
    lseq_as_nat (as_seq h1 mHashRPart) == nat_from_bytes_le hashS % pow2 (8 * v l1))


let ecdsa_signature_step12_lemma cur h c h0 h1 mHash mHashHPart hashS = 
  let mHashRPart = gsub mHash (size 0) c in 
  let mHashHPartLeft = gsub mHash h c in 
  let mHashRPartLeft = gsub mHash c h in 

  lemma_test (as_seq h0 mHash) (v h);
  lemma_test (as_seq h1 mHash) (v h);
  lemma_test (as_seq h1 mHash) (v c);

  assert(lseq_as_nat hashS % (pow2 (8 * (v c))) == (lseq_as_nat (as_seq h1 mHashRPart) + pow2 (8 * (v c)) * lseq_as_nat (as_seq h1 mHashRPartLeft)) % pow2 (8 * (v c)));

  modulo_addition_lemma (lseq_as_nat (as_seq h1 mHashRPart)) (pow2 (8 * (v c))) (lseq_as_nat (as_seq h1 mHashRPartLeft));
  
  assert(lseq_as_nat hashS % (pow2 (8 * (v c))) == (lseq_as_nat (as_seq h1 mHashRPart)) % pow2 (8 * (v c)));
  lseq_upperbound (as_seq h1 mHashRPart);
  small_mod (lseq_as_nat (as_seq h1 mHashRPart)) (pow2 (8 * (v c)));
  
  assert(lseq_as_nat hashS % (pow2 (8 * (v c))) == lseq_as_nat (as_seq h1 mHashRPart));
  lemma_lseq_nat_from_bytes (as_seq h1 mHashRPart);
  lemma_lseq_nat_from_bytes hashS
    

let ecdsa_signature_step12 #c alg mLen m result = 
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  push_frame(); 
  let sz_hash: FStar.UInt32.t = match alg with |NoHash -> mLen |Hash a -> hash_len a in

  let len: FStar.UInt32.t  = sz_hash +! getCoordinateLenU c in 
  let mHash = create len (u8 0) in 
    let h0 = ST.get() in 
    let mHashHPart = sub mHash (size 0) sz_hash in 
    let mHashRPart = sub mHash (size 0) (getCoordinateLenU c) in 
    let mHashHPartLeft = sub mHash sz_hash (getCoordinateLenU c) in 
    let mHashLeft = sub mHash (getCoordinateLenU c) sz_hash in 
    
  begin
  match alg with 
    |NoHash -> copy mHashHPart m 
    |Hash a -> match a with 
      |SHA2_256 -> hash_256 m mLen mHashHPart
      |SHA2_384 -> hash_384 m mLen mHashHPart
      |SHA2_512 -> hash_512 m mLen mHashHPart 
  end;
    let h1 = ST.get() in 
  toUint64ChangeEndian #c mHashRPart result;
    let h2 = ST.get() in 
  reduction_prime_2prime_order result result;
  pop_frame();
      let h3 = ST.get() in 

  lemma_create_zero_buffer #U8 (v len) c;
  ecdsa_signature_step12_lemma c sz_hash (getCoordinateLenU c) h0 h1 mHash mHashHPart (as_seq h1 mHashHPart);

  lemma_lseq_nat_from_bytes (as_seq h1 mHashRPart);
  lemma_nat_from_to_intseq_le_preserves_value #U8 #SEC (getCoordinateLen c) (as_seq h1 mHashRPart);
  lemma_lseq_nat_from_bytes (as_seq h2 result)



#push-options "--ifuel 1"
inline_for_extraction
val ecdsa_signature_step45: #c: curve
  -> x: felem c
  -> k: scalar_t #MUT #c
  -> tempBuffer: lbuffer uint64 (size 20 *! getCoordinateLenU64 c) -> 
  Stack uint64
  (requires fun h -> live h x /\ live h k /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc k; loc x])
  (ensures fun h0 r h1 -> modifies (loc x |+| loc tempBuffer) h0 h1 /\ 
    as_nat c h1 x < getOrder #c /\ (point_mult_0 #c (basePoint #c) 0; 
    let (rxN, ryN, rzN), _ = montgomery_ladder_spec_left #c (as_seq h0 k) (pointAtInfinity, basePoint #c) in 
    let (xN, _, _) = _norm #c (rxN, ryN, rzN) in 
    as_nat c h1 x == xN % getOrder #c /\ (
    if as_nat c h1 x = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0)))

let ecdsa_signature_step45 #c x k tempBuffer = 
  push_frame();
    let len = getCoordinateLenU64 c in 
    let result = create (size 3 *! len) (u64 0) in 
    let tempForNorm = sub tempBuffer (size 0) (size 17 *! len) in 
    secretToPublicWithoutNorm #c result k tempBuffer; 
    normX #c result x tempForNorm;
    reduction_prime_2prime_order x x;
  pop_frame();
    isZero_uint64_CT #c x


#pop-options
inline_for_extraction
val ecdsa_signature_step6: #c: curve -> result: felem c -> kFelem: felem c -> z: felem  c -> r: felem c -> da: felem c -> 
  Stack unit
  (requires fun h -> 
    live h result /\ live h kFelem /\ live h z /\ live h r /\ live h da /\ eq_or_disjoint r da /\ (
    let order = getOrder #c in 
    as_nat c h kFelem < order /\ as_nat c h z < order /\ as_nat c h r < order /\ as_nat c h da < order))
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ (let order = getOrder #c in 
    as_nat c h1 result = (as_nat c h0 z + as_nat c h0 r * as_nat c h0 da) * pow (as_nat c h0 kFelem) (getOrder #c - 2) % order)) 


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
  copy kInv kFelem;
  montgomery_ladder_exponent #c kInv kInv; 
  montgomery_multiplication_buffer_dsa zBuffer kInv result;
    let h6 = ST.get() in 
  pop_frame();

  let r = as_nat c h0 r in 
  let da = as_nat c h0 da in 
  let z = as_nat c h0 z in
  let k = as_nat c h0 kFelem in 

  let order = getOrder #c in 
  let p = modp_inv2_prime (pow2 (getPower c)) order in
  

  
  assert(as_nat c h6 result = toDomain_ #c #DSA (((fromDomain_ #c #DSA r) * (fromDomain_ #c #DSA da) % order + fromDomain_ #c #DSA (fromDomain_ #c #DSA z)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order));

  calc (==) {
    as_nat c h6 result;
  (==) {} 
    toDomain_ #c #DSA (((fromDomain_ #c #DSA r) * (fromDomain_ #c #DSA da) % order + fromDomain_ #c #DSA (fromDomain_ #c #DSA z)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order); 
  (==) {lemmaFromDomain #c #DSA r; lemmaFromDomain #c #DSA da; lemmaFromDomain #c #DSA z}
    toDomain_ #c #DSA (((r * p % order) * (da * p % order) % order + fromDomain_ #c #DSA (z * p % order)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order); 
  (==) {lemmaFromDomain #c #DSA (z * p % order)}
    toDomain_ #c #DSA (((r * p % order) * (da * p % order) % order + ((z * p % order) * p % order)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order); 
  (==) {lemma_mod_mul_distr_l (r * p) (da * p % order) order; lemma_mod_mul_distr_l (z * p) p order}
      toDomain_ #c #DSA ((r * p * (da * p % order) % order + (z * p * p % order)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order); 
   (==) {lemma_mod_mul_distr_r (r * p) (da * p) order}
      toDomain_ #c #DSA ((r * p * (da * p) % order + (z * p * p % order)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order);    
   (==) {lemma_mod_add_distr (r * p * (da * p) % order) (z * p * p) order}
      toDomain_ #c #DSA ((r * p * (da * p) % order + (z * p * p)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order);     
   (==) {lemma_mod_add_distr (z * p * p) (r * p * (da * p)) order}
     toDomain_ #c #DSA ((r * p * (da * p) + (z * p * p)) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order);  
   (==) {assert_by_tactic (r * p * (da * p) + (z * p * p) == (p * p) * (r * da + z)) canon}
     toDomain_ #c #DSA ((p * p) * (r * da + z) % order * (pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order) % order);       
   (==) {lemma_mod_mul_distr_l ((p * p) * (r * da + z)) ((pow (fromDomain_ #c #DSA (as_nat c h0 kFelem)) (order - 2) % order)) order}
     toDomain_ #c #DSA ((p * p) * (r * da + z) * (pow (fromDomain_ #c #DSA k) (order - 2) % order) % order);   
   (==) {lemmaFromDomain #c #DSA k}
     toDomain_ #c #DSA ((p * p) * (r * da + z) * (pow (k * p % order) (order - 2) % order) % order);   
   (==) {power_distributivity (k * p) (order - 2) order} 
     toDomain_ #c #DSA ((p * p) * (r * da + z) * (pow (k * p) (order - 2) % order) % order); 
   (==) {power_distributivity_2 k p (order - 2)}
     toDomain_ #c #DSA ((p * p) * (r * da + z) * (pow k (order - 2) * pow p (order - 2) % order) % order); 
   (==) {lemma_mod_mul_distr_r ((p * p) * (r * da + z)) (pow k (order - 2) * pow p (order - 2)) order}
     toDomain_ #c #DSA ((p * p) * (r * da + z) * (pow k (order - 2) * pow p (order - 2)) % order); 
   (==) {assert_by_tactic ((p * p) * (r * da + z) * (pow k (order - 2) * pow p (order - 2)) == (p * pow p (order - 2)) * (p * ((r * da + z) * pow k (order - 2)))) canon; power_one_2 p}
     toDomain_ #c #DSA ((pow p 1 * pow p (order - 2)) * (p * ((r * da + z) * pow k (order - 2))) % order); 
   (==) {pow_plus p 1 (order - 2)}
     toDomain_ #c #DSA ((pow p (order - 1)) * (p * ((r * da + z) * pow k (order - 2))) % order); 
   (==) {power_as_specification_same_as_fermat p (order - 1)}
     toDomain_ #c #DSA ((FStar.Math.Fermat.pow p (order - 1)) * (p * ((r * da + z) * pow k (order - 2))) % order); 
   (==) {lemma_mod_mul_distr_l (FStar.Math.Fermat.pow p (order - 1)) (p * ((r * da + z) * pow k (order - 2))) order}
     toDomain_ #c #DSA ((FStar.Math.Fermat.pow p (order - 1)) % order * (p * ((r * da + z) * pow k (order - 2))) % order); 
   (==) {Hacl.Impl.EC.Math.lemma_fermat_exp #c}
     toDomain_ #c #DSA (p * ((r * da + z) * pow k (order - 2)) % order); 
   (==) {lemmaFromDomain #c #DSA ((r * da + z) * pow k (order - 2))}
     toDomain_ #c #DSA (fromDomain_ #c #DSA ((r * da + z) * pow k (order - 2))); 
   (==) {lemmaToDomainFromDomainModuloPrime #c #DSA ((r * da + z) * pow k (order - 2))}
     ((r * da + z) * pow k (order - 2)) % order;
  }
  
inline_for_extraction
val ecdsa_signature_core: #c: curve -> alg: hash_alg_ecdsa
  -> r: felem  c
  -> s: felem c
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen 
  -> privKeyAsFelem: felem  c
  -> k: scalar_t #MUT #c  -> 
  Stack uint64
  (requires fun h -> 
    live h r /\ live h s /\ live h m /\ live h privKeyAsFelem /\ live h k /\
    disjoint privKeyAsFelem r /\ disjoint privKeyAsFelem s /\ disjoint k r /\ disjoint r s /\   
    as_nat c h privKeyAsFelem < getOrder #c /\
    nat_from_bytes_be (as_seq h k) < getOrder #c /\ 
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32)
  (ensures fun h0 flag h1 -> modifies (loc r |+| loc s) h0 h1 /\ (
    point_mult_0 #c (basePoint #c) 0; 
    let order = getOrder #c in 
    let z = hashSpec c alg (v mLen) (as_seq h0 m) % order in 
    let baseMultK, _ = montgomery_ladder_spec_left #c (as_seq h0 k) (pointAtInfinity #c, basePoint #c) in 
    let (xN, _, _) = _norm #c baseMultK in 
    let kFelem = nat_from_bytes_be (as_seq h0 k) in 
    as_nat c h1 r == xN % order  /\
    as_nat c h1 s == (z + (as_nat c h1 r) * as_nat c h0 privKeyAsFelem) * pow kFelem (order - 2) % order /\ (
    if as_nat c h1 r = 0 || as_nat c h1 s = 0 then 
      uint_v flag == pow2 64 - 1
    else 
      uint_v flag == 0)))


let ecdsa_signature_core #c alg r s mLen m privKeyAsFelem k = 
  push_frame();
  let h0 = ST.get() in 
    let len : FStar.UInt32.t = getCoordinateLenU64 c in 
    let hashAsFelem = create len (u64 0) in     
    let tempBuffer = create (size 20 *! len) (u64 0) in 
    let kAsFelem = create len (u64 0) in 
    
  toUint64ChangeEndian #c k kAsFelem; 
  ecdsa_signature_step12 #c alg mLen m hashAsFelem; 
  let step5Flag = ecdsa_signature_step45 #c r k tempBuffer in 
  ecdsa_signature_step6 #c s kAsFelem hashAsFelem r privKeyAsFelem; 
  let sIsZero = isZero_uint64_CT #c s in 
  logor_lemma step5Flag sIsZero;
  pop_frame(); 
  logor step5Flag sIsZero


inline_for_extraction noextract
val ecdsa_signature_: #c: curve -> alg : hash_alg_ecdsa 
  -> privKey: scalar_t #MUT #c 
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen 
  -> k: scalar_t #MUT #c 
  -> r: felem c 
  -> s: felem c ->
  Stack bool
  (requires fun h -> live h privKey /\ live h m /\ live h k /\ live h r /\ live h s /\
    disjoint k r /\ disjoint r s /\ disjoint s r /\ 
    nat_from_bytes_be (as_seq h privKey) < getOrder #c /\ 
    nat_from_bytes_be (as_seq h k) < getOrder #c /\
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + getCoordinateLen c < pow2 32)
  (ensures fun h0 f h1 -> modifies ( loc r |+| loc s) h0 h1 /\ (
    let r_, s_, flag = ecdsa_signature c alg (v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
    as_nat c h1 r < pow2 (getPower c) /\ as_nat c h1 s < pow2 (getPower c) /\
    as_nat c h1 r == r_ /\ as_nat c h1 s == s_ /\  f == flag))

let ecdsa_signature_ #c alg privKey mLen m k r s = 
  push_frame();
    let privKeyAsFelem = create (getCoordinateLenU64 c) (u64 0) in 
  toUint64ChangeEndian #c privKey privKeyAsFelem; 
  let flagU64 = ecdsa_signature_core #c alg r s mLen m privKeyAsFelem k in
  let open Hacl.Impl.EC.LowLevel.RawCmp in 
  pop_frame();
  unsafe_bool_of_u64 flagU64


inline_for_extraction noextract
val ecdsa_signature: #c: curve 
  -> alg: hash_alg_ecdsa 
  -> result: pointAffine8 c
  -> mLen: size_t {v mLen >= Spec.ECDSA.min_input_length #c alg}
  -> m: lbuffer uint8 mLen 
  -> privKey: scalar_t #MUT #c
  -> k: scalar_t #MUT #c -> 
  Stack bool
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    (match alg with |NoHash -> v mLen |Hash a -> v (hash_len a)) + v (getCoordinateLenU c) < pow2 32 /\
    nat_from_bytes_be (as_seq h k) < getOrder #c /\
    nat_from_bytes_be (as_seq h privKey) < getOrder #c /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k)
  (ensures fun h0 flag h1 -> modifies (loc result) h0 h1 /\ (
    let resultR = gsub result (size 0) (getCoordinateLenU c) in 
    let resultS = gsub result (getCoordinateLenU c) (getCoordinateLenU c) in 
    let r, s, flagSpec = ecdsa_signature c alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
    as_seq h1 resultR == nat_to_bytes_be (v (getCoordinateLenU c)) r /\
    as_seq h1 resultS == nat_to_bytes_be (v (getCoordinateLenU c)) s /\
    flag == flagSpec))


let ecdsa_signature #c alg result mLen m privKey k = 
  push_frame();
  let h0 = ST.get() in 
    let len: FStar.UInt32.t = getCoordinateLenU64 c in 
    let r = create len (u64 0) in 
    let s = create len (u64 0) in 
    let resultR = sub result (size 0) (getCoordinateLenU c) in 
    let resultS = sub result (getCoordinateLenU c) (getCoordinateLenU c) in 

  let flag = ecdsa_signature_ #c alg privKey mLen m k r s in
  let h1 = ST.get() in 
  fromForm #c r resultR;
  fromForm #c s resultS;

  pop_frame();
  flag  
