module SHA_helpers

open Opaque_s
open Spec.SHA2Again
open X64.CryptoInstructions_s
open Types_s
open Words_s
open FStar.Seq
open FStar.UInt32  // Interop with UInt-based SHA spec

unfold
let (.[]) = FStar.Seq.index

let ws_opaque = make_opaque ws
let shuffle_core_opaque = make_opaque shuffle_core

let make_hash_def (abef cdgh:quad32) : hash_w SHA2_256 =
    let a = uint_to_t abef.hi3 in
    let b = uint_to_t abef.hi2 in
    let c = uint_to_t cdgh.hi3 in
    let d = uint_to_t cdgh.hi2 in
    let e = uint_to_t abef.lo1 in
    let f = uint_to_t abef.lo0 in
    let g = uint_to_t cdgh.lo1 in
    let h = uint_to_t cdgh.lo0 in
    let hash = seq_of_list [a; b; c; d; e; f; g; h] in
    assert_norm (length hash == 8);
    assert_norm (index hash 2 == c);
    hash

let make_hash = make_opaque make_hash_def

let make_hash_properties (abef cdgh:quad32) : 
  Lemma (let hash = make_hash abef cdgh in
         length hash == 8 /\
         hash.[0] == uint_to_t abef.hi3 /\
         hash.[1] == uint_to_t abef.hi2 /\
         hash.[2] == uint_to_t cdgh.hi3 /\
         hash.[3] == uint_to_t cdgh.hi2 /\
         hash.[4] == uint_to_t abef.lo1 /\
         hash.[5] == uint_to_t abef.lo0 /\
         hash.[6] == uint_to_t cdgh.lo1 /\
         hash.[7] == uint_to_t cdgh.lo0)
  = 
  reveal_opaque make_hash_def;
  let hash = make_hash abef cdgh in
  let hash' = make_hash_def abef cdgh in
  assert(hash == hash');
  assert_norm (length hash' == 8);
  assert_norm(hash'.[0] == uint_to_t abef.hi3); 
  assert_norm(hash'.[1] == uint_to_t abef.hi2); 
  assert_norm(hash'.[2] == uint_to_t cdgh.hi3); 
  assert_norm(hash'.[3] == uint_to_t cdgh.hi2); 
  assert_norm(hash'.[4] == uint_to_t abef.lo1); 
  assert_norm(hash'.[5] == uint_to_t abef.lo0); 
  assert_norm(hash'.[6] == uint_to_t cdgh.lo1); 
  assert_norm(hash'.[7] == uint_to_t cdgh.lo0);
  ()

let shuffle_core_properties (a:hash_alg) (block:block_w a) (hash:hash_w a) (t:counter{t < size_k_w a}) :
    Lemma(let h = shuffle_core a block hash t in
          let a0 = hash.[0] in
          let b0 = hash.[1] in
          let c0 = hash.[2] in
          let d0 = hash.[3] in
          let e0 = hash.[4] in
          let f0 = hash.[5] in
          let g0 = hash.[6] in
          let h0 = hash.[7] in
          let t1 = word_add_mod a h0 (word_add_mod a (_Sigma1 a e0) (word_add_mod a (_Ch a e0 f0 g0) (word_add_mod a (k0 a).[t] (ws a block t)))) in
          let t2 = word_add_mod a (_Sigma0 a a0) (_Maj a a0 b0 c0) in         
          h.[0] == word_add_mod a t1 t2 /\
          h.[1] == a0 /\
          h.[2] == b0 /\
          h.[3] == c0 /\
          h.[4] == word_add_mod a d0 t1 /\
          h.[5] == e0 /\
          h.[6] == f0 /\
          h.[7] == g0)
  =
  let h = shuffle_core a block hash t in
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in
  let t1 = word_add_mod a h0 (word_add_mod a (_Sigma1 a e0) (word_add_mod a (_Ch a e0 f0 g0) (word_add_mod a (k0 a).[t] (ws a block t)))) in
  let t2 = word_add_mod a (_Sigma0 a a0) (_Maj a a0 b0 c0) in         
  assert(h.[0] == word_add_mod a t1 t2);
  assert(h.[1] == a0);
  assert(h.[2] == b0);
  assert(h.[3] == c0);
  assert(h.[4] == word_add_mod a d0 t1);
  assert(h.[5] == e0);
  assert(h.[6] == f0);
  assert(h.[7] == g0);
//  assert_norm(h.[0] == word_add_mod a t1 t2);
//  assert_norm(h.[1] == a0);
//  assert_norm(h.[2] == b0);
//  assert_norm(h.[3] == c0);
//  assert_norm(h.[4] == word_add_mod a d0 t1);
//  assert_norm(h.[5] == e0);
//  assert_norm(h.[6] == f0);
//  assert_norm(h.[7] == g0);
  ()


//#push-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 2 --initial_ifuel 2 --z3rlimit 30"  
let lemma_sha256_rnds2 (abef cdgh xmm0:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires t + 1 < size_k_w SHA2_256 /\
            xmm0.lo0 == v (add_mod (index (k0 SHA2_256) t)     (ws_opaque SHA2_256 block t)) /\
            xmm0.lo1 == v (add_mod (index (k0 SHA2_256) (t+1)) (ws_opaque SHA2_256 block (t+1))))
  (ensures (let hash0 = make_hash abef cdgh in
            let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
            let hash2 = shuffle_core_opaque SHA2_256 block hash1 t in
            hash2 == make_hash (sha256_rnds2_spec cdgh abef xmm0) abef))
  =
  reveal_opaque ws;
  reveal_opaque shuffle_core;
  reveal_opaque make_hash_def;
  let hash0 = make_hash abef cdgh in
  let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
  let hash1' = shuffle_core SHA2_256 block hash0 t in
  let hash2 = shuffle_core_opaque SHA2_256 block hash1 t in
  make_hash_properties abef cdgh;
  let a1,b1,c1,d1,e1,f1,g1,h1 = sha256_rnds2_spec_update 
                 hash0.[0]
                 hash0.[1]
                 hash0.[2]
                 hash0.[3]
                 hash0.[4]
                 hash0.[5]
                 hash0.[6]
                 hash0.[7]
                 (uint_to_t xmm0.lo0) 
  in
  //assert_norm (hash0.[0] == b1);  // Fails
  assert (b1 == hash0.[0]);   // Passes
  //assert (b1 == hash1'.[1]);  // Fails
  assert_norm (b1 == hash1'.[1]); 
//  assert_norm (hash1'.[1] == b1);

  make_hash_properties (sha256_rnds2_spec cdgh abef xmm0) abef;
  
  admit();
  ()
  
//#pop-options
