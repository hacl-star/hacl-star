module SHA_helpers

open Opaque_s
open Spec.SHA2Again
open X64.CryptoInstructions_s
open Types_s
open Words_s
open FStar.Seq
open FStar.UInt32  // Interop with UInt-based SHA spec
open Arch.Types

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
  admit();
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
            let hash2 = shuffle_core_opaque SHA2_256 block hash1 (t + 1) in
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

let ws_quad32 (t:counter) (block:block_w SHA2_256) : quad32 =
    if t < size_k_w SHA2_256 - 3 then
       Mkfour (v (ws_opaque SHA2_256 block t))
              (v (ws_opaque SHA2_256 block (t+1)))
              (v (ws_opaque SHA2_256 block (t+2)))
              (v (ws_opaque SHA2_256 block (t+3)))
    else 
       Mkfour 0 0 0 0

let _sigma0_quad32 (q:quad32) : quad32 =
  Mkfour (v (_sigma0 SHA2_256 (uint_to_t q.lo0)))
         (v (_sigma0 SHA2_256 (uint_to_t q.lo1)))
         (v (_sigma0 SHA2_256 (uint_to_t q.hi2)))
         (v (_sigma0 SHA2_256 (uint_to_t q.hi3)))

let ws_partial_def (t:counter) (block:block_w SHA2_256) : quad32 =
    if 16 <= t && t < size_k_w SHA2_256 then
       (let init = ws_quad32 (t-16) block in
        let sigma0_in = ws_quad32 (t-15) block in
        let sigma0_out = _sigma0_quad32 sigma0_in in
        add_wrap_quad32 init sigma0_out)
    else 
       Mkfour 0 0 0 0

let ws_partial = make_opaque ws_partial_def

let lemma_add_wrap_is_add_mod (n0 n1:nat32) :
  Lemma (add_wrap n0 n1 == v(add_mod (uint_to_t n0) (uint_to_t n1)))
  =
  ()

let add_mod_quad32 (q0 q1:quad32) : quad32 =
  Mkfour (v (add_mod (uint_to_t q0.lo0) (uint_to_t q1.lo0)))
         (v (add_mod (uint_to_t q0.lo1) (uint_to_t q1.lo1)))
         (v (add_mod (uint_to_t q0.hi2) (uint_to_t q1.hi2)))
         (v (add_mod (uint_to_t q0.hi3) (uint_to_t q1.hi3)))

let lemma_add_wrap_quad32_is_add_mod_quad32 (q0 q1:quad32) :
  Lemma (add_mod_quad32 q0 q1 == add_wrap_quad32 q0 q1)
  =
  ()

let lemma_sha256_msg1 (dst src:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) /\
            dst == ws_quad32 (t-16) block /\
            src.lo0 == v(ws_opaque SHA2_256 block (t-12)))
  (ensures sha256_msg1_spec dst src == ws_partial t block)
  =
  reveal_opaque sha256_msg1_spec_def;
  let init = ws_quad32 (t-16) block in
  let sigma0_in = ws_quad32 (t-15) block in
  let sigma0_out = _sigma0_quad32 sigma0_in in
  lemma_add_wrap_quad32_is_add_mod_quad32 init sigma0_out;
  reveal_opaque ws_partial_def;
  ()
  
let lemma_add_mod_commutes (x y:UInt32.t) :
  Lemma (add_mod x y == add_mod y x)
  =
  ()

let lemma_add_mod32_associates (x y z:int) :
  Lemma ( ((x + y % pow2_32) + z) % pow2_32 == (x + ((y + z) % pow2_32)) % pow2_32 )
  =
  ()

#push-options "--z3rlimit 20"
let lemma_add_mod_associates_U32 (x y z:UInt32.t) :
  Lemma (add_mod x (add_mod y z) == add_mod (add_mod x y) z)
  =
  //assert (add_mod y z == uint_to_t ((v y + v z) % pow2_32));
  //assert (add_mod x (add_mod y z) == uint_to_t ((v x + v (uint_to_t ((v y + v z) % pow2_32))) % pow2_32));
  lemma_add_mod32_associates (v x) (v y) (v z);
  (*
  assert (uint_to_t ((v x + v (uint_to_t ((v y + v z) % pow2_32))) % pow2_32) ==
          uint_to_t (((v x + v y % pow2_32) + v z) % pow2_32));
          *)
  assert (add_mod (add_mod x y) z == uint_to_t (((v x + v y % pow2_32) + v z) % pow2_32));
  //admit();
  ()
#pop-options

let lemma_add_mod_ws_rearrangement (a b c d:UInt32.t) :
  Lemma (add_mod a (add_mod b (add_mod c d)) == add_mod (add_mod b (add_mod d c)) a)
  =
  lemma_add_mod_commutes (add_mod b (add_mod d c)) a;
  assert (add_mod (add_mod b (add_mod d c)) a == add_mod a (add_mod b (add_mod d c)));
  lemma_add_mod_commutes c d;
  assert (add_mod a (add_mod b (add_mod d c)) == add_mod a (add_mod b (add_mod c d)));
  ()

let ws_computed (a:hash_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
  if t < size_block_w then ws_opaque a b t
  else
    let t16 = ws_opaque a b (t - 16) in
    let t15 = ws_opaque a b (t - 15) in
    let t7  = ws_opaque a b (t - 7) in
    let t2  = ws_opaque a b (t - 2) in
    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    (word_add_mod a s1 (word_add_mod a t7 (word_add_mod a s0 t16)))

let lemma_ws_computed_is_ws (b:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256}) :
  Lemma (ws_computed SHA2_256 b t == ws SHA2_256 b t)
  =
  if t < size_block_w then (
    assert (ws_computed SHA2_256 b t == ws_opaque SHA2_256 b t);
    reveal_opaque ws;
    assert (ws_opaque SHA2_256 b t == ws SHA2_256 b t);
    ()
  ) else (
    let t16 = ws_opaque SHA2_256 b (t - 16) in
    let t15 = ws_opaque SHA2_256 b (t - 15) in
    let t7  = ws_opaque SHA2_256 b (t - 7) in
    let t2  = ws_opaque SHA2_256 b (t - 2) in
    let s1 = _sigma1 SHA2_256 t2 in
    let s0 = _sigma0 SHA2_256 t15 in
    lemma_add_mod_ws_rearrangement s1 t7 s0 t16;
    reveal_opaque ws;
    ()
  );
  ()

let add_wrap_quad32 (q0 q1:quad32) : quad32 =
  Mkfour (v (add_mod (uint_to_t q0.lo0) (uint_to_t q1.lo0)))
         (v (add_mod (uint_to_t q0.lo1) (uint_to_t q1.lo1)))
         (v (add_mod (uint_to_t q0.hi2) (uint_to_t q1.hi2)))
         (v (add_mod (uint_to_t q0.hi3) (uint_to_t q1.hi3))) 

let test  (t:counter{t < size_k_w SHA2_256 - 3}) (block:block_w SHA2_256) : nat32 =
  let c:UInt32.t = ws_computed SHA2_256 block t in
  v c

let test2 (u:UInt32.t) : nat32 =
  v u

#reset-options "--z3rlimit 20"
let ws_computed_quad32 (t:counter{t < size_k_w SHA2_256 - 3}) (block:block_w SHA2_256) : quad32 =
       Mkfour (v (ws_computed SHA2_256 block t))
              (v (ws_computed SHA2_256 block (t+1)))
              (v (ws_computed SHA2_256 block (t+2)))
              (v (ws_computed SHA2_256 block (t+3)))

let test (src1 src2:quad32) (t:counter{t >= 16 /\ t < size_k_w SHA2_256}) (block:block_w SHA2_256) =
    assume (src2.lo0 == v (ws_opaque SHA2_256 block t - 12));
    assume (src1.hi2 == v (ws_opaque SHA2_256 block (t-2)));
    assume (src1.hi3 == v (ws_opaque SHA2_256 block (t-1))); 
    let dst = ws_quad32 (t-16) block in
    let w = sha256_msg1_spec_def dst src2 in
    let mid = ws_quad32 (t - 7) block in
    let added = add_mod_quad32 mid w in
    let final = sha256_msg2_spec_def added in
    assert (final == ws_computed_quad32 t block);
    ()

(*
#push-options "--z3rlimit 10"
let lemma_sha256_msg2 (dst src:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) /\
            src.hi2 == v (ws_opaque SHA2_256 block (t-2)) /\
            src.hi3 == v (ws_opaque SHA2_256 block (t-1)) /\
            (let w = ws_partial t block in
             let mid = ws_quad32 (t-7) block in
             dst == add_wrap_quad32 mid w))
  (ensures sha256_msg2_spec dst src == ws_quad32 t block)
  =
  reveal_opaque sha256_msg2_spec_def;
  let init = ws_quad32 (t-16) block in
  let sigma0_in = ws_quad32 (t-15) block in
  //assert (t - 15 < size_k_w SHA2_256 - 3);
  let sigma0_out = _sigma0_quad32 sigma0_in in
  let w = ws_partial t block in
  let mid = ws_quad32 (t-7) block in
  lemma_add_wrap_quad32_is_add_mod_quad32 mid w;
  assert (dst == add_mod_quad32 mid w);
  //
  let result = sha256_msg2_spec dst src in
  //assert (result.lo0 == v (add_mod (uint_to_t dst.lo0) (_sigma1 SHA2_256 (uint_to_t src.hi2))));
  //assert (sigma0_in.lo0 == v (ws_opaque SHA2_256 block (t-15)));
  reveal_opaque ws_partial_def;
  lemma_add_wrap_quad32_is_add_mod_quad32 init sigma0_out;
  assert (w == add_mod_quad32 init sigma0_out);
  (*
  assert (dst.lo0 == add_wrap (v (ws_opaque SHA2_256 block (t-7))) (add_wrap init.lo0 sigma0_out.lo0));
  assert (sigma0_out.lo0 == (v (_sigma0 SHA2_256 (uint_to_t sigma0_in.lo0))));
  assert (sigma0_out.lo0 == (v (_sigma0 SHA2_256 (uint_to_t (v (ws_opaque SHA2_256 block (t-15)))))));
  assert (init.lo0 ==  (v (ws_opaque SHA2_256 block (t-16))));
  assert (dst.lo0 == add_wrap (v (ws_opaque SHA2_256 block (t-7))) 
                    (add_wrap (v (ws_opaque SHA2_256 block (t-16)))
                              (v (_sigma0 SHA2_256 (uint_to_t (v (ws_opaque SHA2_256 block (t-15))))))));  
  assert (result.lo0 == v (add_mod (uint_to_t dst.lo0) 
                                   (_sigma1 SHA2_256 (uint_to_t src.hi2))));
  assert (result.lo0 == v (add_mod (uint_to_t dst.lo0) 
                                   (_sigma1 SHA2_256 (uint_to_t (v (ws_opaque SHA2_256 block (t-2)))))));
  *)
  (*                                   
  assert (result.lo0 == v (add_mod (uint_to_t (add_wrap (v (ws_opaque SHA2_256 block (t-7))) 
                                                        (add_wrap #32 (v (ws_opaque SHA2_256 block (t-16)))
                                                                  (v (_sigma0 SHA2_256 (uint_to_t (v (ws_opaque SHA2_256 block (t-15)))))))))
                                   (_sigma1 SHA2_256 (uint_to_t (v (ws_opaque SHA2_256 block (t-2)))))));
  *)
//  reveal_opaque ws;
  admit();
  ()
#pop-options
*)
