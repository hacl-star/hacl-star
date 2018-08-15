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
  make_hash_properties abef cdgh;
  make_hash_properties (sha256_rnds2_spec cdgh abef xmm0) abef;
  //admit();
  ()
