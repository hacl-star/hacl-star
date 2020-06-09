module Hacl.Impl.ECDSA.Defensive

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteSequence

open Spec.ECDSAP256.Definition

open Spec.Hash.Definitions
open Hacl.Impl.P256.LowLevel

open Spec.ECDSA
open Spec.P256.Lemmas
open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.P256.Signature.Agile

open Lib.Memzero


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

val cleanUpCritical: critical : lbuffer uint64 (size 4) -> Stack unit
  (requires fun h -> live h critical)
  (ensures fun h0 _ h1 -> modifies (loc critical) h0 h1 /\ as_seq h1 critical == Seq.create 4 (u64 0))

let cleanUpCritical critical = 
  clear_words_u64 4ul critical


open Lib.IntTypes.Intrinsics
open FStar.Mul

val sub4: x: felem ->  result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ (if (nat_from_intseq_be (as_seq h0 x) >= prime_p256_order) then uint_v c = 0 else uint_v c = 1))

let sub4 x result = 
  let h0 = ST.get() in 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);

    let cc0 = sub_borrow_u64 (u64 0) x.(size 3) prime256order_buffer.(size 0) r0 in 
      let h1 = ST.get() in 
    let cc1 = sub_borrow_u64 cc0 x.(size 2) prime256order_buffer.(size 1) r1 in 
      let h2 = ST.get() in 
    let cc2 = sub_borrow_u64 cc1 x.(size 1) prime256order_buffer.(size 2) r2 in 
      let h3 = ST.get() in 
    let cc3 = sub_borrow_u64 cc2 x.(size 0) prime256order_buffer.(size 3) r3 in 
      let h4 = ST.get() in 

    let open Lib.Sequence in 

    nat_from_intseq_be_slice_lemma (as_seq h0 x) 3;
    nat_from_intseq_be_slice_lemma (slice (as_seq h0 x) 0 3) 2;
    nat_from_intseq_be_slice_lemma (slice (as_seq h0 x) 0 2) 1;
    
    nat_from_intseq_be_lemma0 (slice (as_seq h0 x) 3 4);
    nat_from_intseq_be_lemma0 (slice (as_seq h0 x) 2 3);
    nat_from_intseq_be_lemma0 (slice (as_seq h0 x) 1 2);
    nat_from_intseq_be_lemma0 (slice (as_seq h0 x) 0 1);

    assert(disjoint prime256order_buffer result);
    
    cc3
    


val lessThanOrderU8: i: lbuffer uint8 (size 32) -> critical: lbuffer uint64 (size 4) -> critical1: lbuffer uint64 (size 4) -> Stack uint64 
  (requires fun h -> live h i /\ live h critical /\ live h critical1 /\ disjoint i critical /\ disjoint critical critical1)
  (ensures fun h0 r h1 -> modifies (loc critical |+| loc critical1) h0 h1 /\ (uint_v r == 0 <==> nat_from_bytes_be (as_seq h0 i) < prime_p256_order))

let lessThanOrderU8 i critical critical1 = 
    let h0 = ST.get() in 
  toUint64 i critical;
    let h1 = ST.get() in 
    Lib.ByteSequence.uints_from_bytes_be_nat_lemma #U64 #_ #4 (as_seq h0 i);
    
  let carry = sub4 critical  critical1 in 
  let less = eq_mask carry (u64 0) in 
  eq_mask_lemma carry (u64 0);
  less


(* This function is not SC resistant *)
val compareTo0TwoVariablesNotSC: a: uint64 -> b: uint64 ->
  Tot (r : bool {r = (uint_v a = 0 && uint_v b = 0)})

let compareTo0TwoVariablesNotSC a b = 
  let open Hacl.Impl.P256.LowLevel.RawCmp in 
  let firstZero = eq_0_u64 a in 
  let secondZero = eq_0_u64 b in 
  firstZero && secondZero
  

val ecdsa_signature_defensive: alg: hash_alg_ecdsa 
  -> result: lbuffer uint8 (size 64) 
  -> mLen: size_t 
  -> m: lbuffer uint8 mLen 
  -> privKey: lbuffer uint8 (size 32) 
  -> k: lbuffer uint8 (size 32) -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k
  )
  (ensures fun h0 flag h1 ->
    modifies (loc result) h0 h1 /\
    (
      if (alg = NoHash || alg = Hash SHA2_256 || alg = Hash SHA2_384 || alg = Hash SHA2_512) && (v mLen >= Spec.ECDSA.min_input_length alg) && (nat_from_bytes_be (as_seq h0 privKey) < prime_p256_order) &&  (nat_from_bytes_be (as_seq h0 k) < prime_p256_order) then 
      (
	let resultR = gsub result (size 0) (size 32) in 
	let resultS = gsub result (size 32) (size 32) in 
	let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
	as_seq h1 resultR == nat_to_bytes_be 32 r /\
	as_seq h1 resultS == nat_to_bytes_be 32 s /\
	flag == flagSpec  
      )
      else 
	v flag == pow2 64 - 1
  ) 
)

let ecdsa_signature_defensive alg result mLen m privKey k = 
  push_frame();  
  admit();
  let cr0 = create (size 4) (u64 0) in 
  let cr1 = create (size 4) (u64 0) in  
  let sizeCheck = gte mLen (min_input_length_v alg) in   
  let algorithm = (* (alg = NoHash || alg = Hash SHA2_256 || alg = Hash SHA2_384 || alg = Hash SHA2_512) *) true in 
  if algorithm && sizeCheck  then 
    begin
      let less0 = lessThanOrderU8 privKey cr0 cr1 in 
      let less1 = lessThanOrderU8 k cr0 cr1 in 
      let flagLessOrder = compareTo0TwoVariablesNotSC less0 less1 in 
	  if flagLessOrder then 
	    begin
	      let h1 = ST.get() in 
	      let r = ecdsa_signature_defensive alg result mLen m privKey k cr0 cr1 in 
	      cleanUpCritical cr0;
	      cleanUpCritical cr1;
	      pop_frame();
	      r
	    end
	  else
	    begin 
	      pop_frame();
	      u64 (normalize_term (maxint U64))
	    end 
    end
  else 
    begin
      pop_frame();
      u64 (normalize_term (maxint U64))
    end




val ecdsa_signature_defensive2: alg: hash_alg_ecdsa 
  -> result: lbuffer uint8 (size 64) 
  -> mLen: size_t 
  -> m: lbuffer uint8 mLen 
  -> keyLen: size_t 
  -> privKey: lbuffer uint8 keyLen
  -> nonceLen: size_t
  -> k: lbuffer uint8 nonceLen -> 
  Stack uint64
  (requires fun h -> 
    live h result /\ live h m /\ live h privKey /\ live h k /\
    disjoint result m /\
    disjoint result privKey /\
    disjoint result k
  )
  (ensures fun h0 flag h1 ->
     modifies (loc result) h0 h1 /\ 
    (
      if (alg = NoHash || alg = Hash SHA2_256 || alg = Hash SHA2_384 || alg = Hash SHA2_512) && 
	(v mLen >= Spec.ECDSA.min_input_length alg) && 
	(nat_from_bytes_be (as_seq h0 privKey) < prime_p256_order) && 
	(nat_from_bytes_be (as_seq h0 k) < prime_p256_order)  && 
	(uint_v keyLen = 32) &&
	(uint_v nonceLen = 32) 
	then 
      (
	let resultR = gsub result (size 0) (size 32) in 
	let resultS = gsub result (size 32) (size 32) in 
	let r, s, flagSpec = Spec.ECDSA.ecdsa_signature_agile alg (uint_v mLen) (as_seq h0 m) (as_seq h0 privKey) (as_seq h0 k) in 
	as_seq h1 resultR == nat_to_bytes_be 32 r /\
	as_seq h1 resultS == nat_to_bytes_be 32 s /\
	flag == flagSpec  
      )
      else 
	v flag == pow2 64 - 1
  ) 
)


let ecdsa_signature_defensive2 alg result mLen m keyLen privKey nonceLen k = 
  push_frame();  
    let h0 = ST.get() in 

  let crTemp = create (size 8) (u64 0) in 
    let cr0 = sub crTemp (size 0) (size 4) in 
    let cr1 = sub crTemp (size 4) (size 4) in  

  let criticalData = create (size 64) (u8 0) in 
    let criticalKey = sub criticalData (size 0) (size 32) in 
    let criticalNonce = sub criticalData (size 32) (size 32) in 

  let lenKeyCorrect = eq keyLen (size 32) in 
  let lenNonceCorrect = eq nonceLen (size 32) in 

  let lenMessCorrect = gte mLen (min_input_length_v alg) in   
  
  if (alg = NoHash || alg = Hash SHA2_256 || alg = Hash SHA2_384 || alg = Hash SHA2_512) && lenMessCorrect && lenKeyCorrect && lenNonceCorrect then 
    begin
      let less0 = lessThanOrderU8 privKey cr0 cr1 in 
      let less1 = lessThanOrderU8 k cr0 cr1 in 
      let flagLessOrder = compareTo0TwoVariablesNotSC less0 less1 in 
	  if flagLessOrder then 
	    begin
	      copy criticalKey privKey;
	      copy criticalNonce k;

	      let flag = Hacl.Impl.ECDSA.P256.Signature.Agile.ecdsa_signature_defensive alg result mLen m criticalKey criticalNonce cr0 cr1 in
	      clear_words_u64 8ul crTemp;
	      clear_words_u8 64ul criticalData;
	      pop_frame();
	      flag
	    end
	  else
	    begin 
	      pop_frame();
	      u64 (normalize_term (maxint U64))
	    end 
    end
  else 
    begin
      pop_frame();
      u64 (normalize_term (maxint U64))
    end
