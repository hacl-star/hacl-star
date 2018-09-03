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

#reset-options "--max_fuel 0 --max_ifuel 0"

// Define these specific converters here, so that F* only reasons about 
// the correctness of the conversion once, rather that at every call site
let vv (u:UInt32.t) : nat32 = v u
let to_uint32 (n:nat32) : UInt32.t = uint_to_t n

unfold let ws_opaque = make_opaque ws
unfold let shuffle_core_opaque = make_opaque shuffle_core

let make_hash_def (abef cdgh:quad32) :
    (hash:hash_w SHA2_256 {
         length hash == 8 /\
         hash.[0] == to_uint32 abef.hi3 /\
         hash.[1] == to_uint32 abef.hi2 /\
         hash.[2] == to_uint32 cdgh.hi3 /\
         hash.[3] == to_uint32 cdgh.hi2 /\
         hash.[4] == to_uint32 abef.lo1 /\
         hash.[5] == to_uint32 abef.lo0 /\
         hash.[6] == to_uint32 cdgh.lo1 /\
         hash.[7] == to_uint32 cdgh.lo0    
    } ) =
    let a = to_uint32 abef.hi3 in
    let b = to_uint32 abef.hi2 in
    let c = to_uint32 cdgh.hi3 in
    let d = to_uint32 cdgh.hi2 in
    let e = to_uint32 abef.lo1 in
    let f = to_uint32 abef.lo0 in
    let g = to_uint32 cdgh.lo1 in
    let h = to_uint32 cdgh.lo0 in
    let l = [a; b; c; d; e; f; g; h] in
    let hash = seq_of_list l in
    assert_norm (length hash == 8);
    elim_of_list l;
    //assert_norm (index hash 2 == c);
    hash

unfold let make_hash = make_opaque make_hash_def

let shuffle_core_properties (a:hash_alg) (block:block_w a) (hash:hash_w a) (t:counter{t < size_k_w a}) :
    Lemma(let h = shuffle_core_opaque a block hash t in
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
  reveal_opaque shuffle_core;
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
  let l = [ word_add_mod a t1 t2; a0; b0; c0; word_add_mod a d0 t1; e0; f0; g0 ] in
  assert (h == seq_of_list l);
  elim_of_list l;
  ()

let sha256_rnds2_spec_update_quad32 (abef cdgh:quad32) (wk:word SHA2_256) : (quad32*quad32) =
  let hash0 = make_hash abef cdgh in
  let a', b', c', d', e', f', g', h' = sha256_rnds2_spec_update hash0.[0] hash0.[1] hash0.[2] hash0.[3] hash0.[4] hash0.[5] hash0.[6] hash0.[7] wk in
  let abef' = Mkfour (vv f') (vv e') (vv b') (vv a') in
  let cdgh' = Mkfour (vv h') (vv g') (vv d') (vv c') in
  (abef', cdgh')

let sha256_rnds2_spec_quad32 (src1 src2 wk:quad32) : quad32 =
  let abef', cdgh'   = sha256_rnds2_spec_update_quad32 src2 src1   (to_uint32 wk.lo0) in
  let abef'', cdgh'' = sha256_rnds2_spec_update_quad32 abef' cdgh' (to_uint32 wk.lo1) in
  abef''

let lemma_sha256_rnds2_spec_quad32 (src1 src2 wk:quad32) :
  Lemma (sha256_rnds2_spec src1 src2 wk == sha256_rnds2_spec_quad32 src1 src2 wk)
  =
  reveal_opaque sha256_rnds2_spec_def;
  ()

let lemma_add_mod_commutes (x y:UInt32.t) :
  Lemma (add_mod x y == add_mod y x)
  =
  ()

let lemma_add_mod32_associates (x y z:int) :
  Lemma ( ((x + y % pow2_32) + z) % pow2_32 == (x + ((y + z) % pow2_32)) % pow2_32 )
  =
  ()

let lemma_add_mod_associates_U32 (x y z:UInt32.t) :
  Lemma (add_mod x (add_mod y z) == add_mod (add_mod x y) z)
  =
  assert_norm (pow2 32 == pow2_32);
  //assert (add_mod y z == to_uint32 ((vv y + vv z) % pow2_32));
  //assert (add_mod x (add_mod y z) == to_uint32 ((vv x + vv (to_uint32 ((vv y + vv z) % pow2_32))) % pow2_32));
  lemma_add_mod32_associates (vv x) (vv y) (vv z);
  //assert (to_uint32 ((vv x + vv (to_uint32 ((vv y + vv z) % pow2_32))) % pow2_32) ==
  //        to_uint32 (((vv x + vv y % pow2_32) + vv z) % pow2_32));
  admit() // TODO: This proof is flaky.  Some combination of the asserts above will make it go through, but the combo varies day by day

let lemma_add_wrap_is_add_mod (n0 n1:nat32) :
  Lemma (add_wrap n0 n1 == vv (add_mod (to_uint32 n0) (to_uint32 n1)))
  =
  assert_norm (pow2 32 == pow2_32);
  ()

let add_wrap_commutes (x y:nat32) :
  Lemma(add_wrap x y == add_wrap y x)
  =
  ()

// Walk F* through the math steps required to rearrange all of the add_mods
let lemma_add_mod_a (a b c d e f g h wk:word SHA2_256) : 
  Lemma ( let u = add_mod (_Ch SHA2_256 e f g) 
                  (add_mod (_Sigma1 SHA2_256 e) 
                  (add_mod wk 
                  (add_mod h 
                  (add_mod (_Maj SHA2_256 a b c) 
                           (_Sigma0 SHA2_256 a))))) in
          let t1 = add_mod h (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) in
          let t2 = add_mod (_Sigma0 SHA2_256 a) (_Maj SHA2_256 a b c) in                      
          let core = add_mod t1 t2 in
          u == core)
  =
  let t1 = add_mod h (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) in
  let t2 = add_mod (_Sigma0 SHA2_256 a) (_Maj SHA2_256 a b c) in                      
  let core = add_mod t1 t2 in
  lemma_add_mod_commutes (_Sigma0 SHA2_256 a) (_Maj SHA2_256 a b c);
  assert (t2 == add_mod (_Maj SHA2_256 a b c) (_Sigma0 SHA2_256 a));
  lemma_add_mod_commutes h (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk));
  assert (t1 == add_mod (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) h);
  lemma_add_mod_associates_U32 (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) h (add_mod (_Maj SHA2_256 a b c) (_Sigma0 SHA2_256 a));
  assert (core == add_mod (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) (add_mod h (add_mod (_Maj SHA2_256 a b c) (_Sigma0 SHA2_256 a))));
  lemma_add_mod_associates_U32 (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g) wk;
  // ==> add_mod (add_mod (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g)) wk)
  lemma_add_mod_commutes (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g);
  // ==> add_mod (add_mod (_Ch SHA2_256 e f g) (_Sigma1 SHA2_256 e)) wk)
  lemma_add_mod_associates_U32 (add_mod (_Ch SHA2_256 e f g) (_Sigma1 SHA2_256 e)) wk (add_mod h (add_mod (_Maj SHA2_256 a b c) (_Sigma0 SHA2_256 a)));
  assert (core == add_mod (add_mod (_Ch SHA2_256 e f g) (_Sigma1 SHA2_256 e)) (add_mod wk (add_mod h (add_mod (_Maj SHA2_256 a b c) (_Sigma0 SHA2_256 a)))));
  lemma_add_mod_associates_U32 (_Ch SHA2_256 e f g) (_Sigma1 SHA2_256 e) (add_mod wk (add_mod h (add_mod (_Maj SHA2_256 a b c) (_Sigma0 SHA2_256 a))));
  ()

let lemma_add_mod_e (a b c d e f g h wk:word SHA2_256) : 
  Lemma ( let u = add_mod (_Ch SHA2_256 e f g)
                  (add_mod (_Sigma1 SHA2_256 e)
                  (add_mod wk 
                  (add_mod h 
                           d))) in
          let t1 = add_mod h (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) in
          let core = add_mod d t1 in
          u == core)
  =
  let t1 = add_mod h (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) in
  let core = add_mod d t1 in
  lemma_add_mod_commutes h (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk));
  // t1 == add_mod (add_mod (_Sigma1 SHA2_256 e) (add_mod (_Ch SHA2_256 e f g) wk)) h);
  lemma_add_mod_commutes d t1;
  // core == add_mod t1 d
  lemma_add_mod_associates_U32 (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g) wk;
  assert (t1 == add_mod (add_mod (add_mod (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g)) wk) h);
  lemma_add_mod_associates_U32 (add_mod (add_mod (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g)) wk) h d;
  assert (core == add_mod (add_mod (add_mod (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g)) wk) (add_mod h d));
  lemma_add_mod_associates_U32 (add_mod (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g)) wk (add_mod h d);
  assert (core == add_mod (add_mod (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g)) (add_mod wk (add_mod h d)));
  lemma_add_mod_commutes (_Sigma1 SHA2_256 e) (_Ch SHA2_256 e f g);
  lemma_add_mod_associates_U32 (_Ch SHA2_256 e f g) (_Sigma1 SHA2_256 e)  (add_mod wk (add_mod h d));
  assert (core == add_mod (_Ch SHA2_256 e f g) (add_mod (_Sigma1 SHA2_256 e) (add_mod wk (add_mod h d))));
  ()

let lemma_sha256_rnds2_spec_update_is_shuffle_core (hash:hash_w SHA2_256) (wk:word SHA2_256) (t:counter) (block:block_w SHA2_256) : Lemma
   (requires t < size_k_w SHA2_256 /\ wk == add_mod (k0 SHA2_256).[t] (ws_opaque SHA2_256 block t))
   (ensures (let a', b', c', d', e', f', g', h' = 
                 sha256_rnds2_spec_update hash.[0] hash.[1] hash.[2] hash.[3] 
                                          hash.[4] hash.[5] hash.[6] hash.[7] wk in
             let u = seq_of_list [a'; b'; c'; d'; e'; f'; g'; h'] in
             let c = shuffle_core_opaque SHA2_256 block hash t in
             u == c))
  =
  let a', b', c', d', e', f', g', h' = 
                 sha256_rnds2_spec_update hash.[0] hash.[1] hash.[2] hash.[3] 
                                          hash.[4] hash.[5] hash.[6] hash.[7] wk in
  let l = [a'; b'; c'; d'; e'; f'; g'; h'] in                                          
  let u = seq_of_list l in
  let c = shuffle_core_opaque SHA2_256 block hash t in
  reveal_opaque shuffle_core;
  reveal_opaque ws;
  shuffle_core_properties SHA2_256 block hash t;
  elim_of_list l;
  lemma_add_mod_a hash.[0] hash.[1] hash.[2] hash.[3] hash.[4] hash.[5] hash.[6] hash.[7] wk;
  lemma_add_mod_e hash.[0] hash.[1] hash.[2] hash.[3] hash.[4] hash.[5] hash.[6] hash.[7] wk;  
  ()


let sha256_rnds2_spec_update_core_quad32 (abef cdgh:quad32) (wk:word SHA2_256) (block:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256}) : (quad32*quad32) =
  let hash0 = make_hash abef cdgh in
  let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
  let abef' = Mkfour (vv hash1.[5]) (vv hash1.[4]) (vv hash1.[1]) (vv hash1.[0]) in
  let cdgh' = Mkfour (vv hash1.[7]) (vv hash1.[6]) (vv hash1.[3]) (vv hash1.[2]) in
  (abef', cdgh')

let lemma_rnds_quad32 (abef cdgh:quad32) (wk:word SHA2_256) (block:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256}) : Lemma
  (requires wk == add_mod (k0 SHA2_256).[t] (ws_opaque SHA2_256 block t))
  (ensures sha256_rnds2_spec_update_core_quad32 abef cdgh wk block t == sha256_rnds2_spec_update_quad32 abef cdgh wk)
  =
  let hash0 = make_hash abef cdgh in
  let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
  let a', b', c', d', e', f', g', h' = 
                 sha256_rnds2_spec_update hash0.[0] hash0.[1] hash0.[2] hash0.[3] 
                                          hash0.[4] hash0.[5] hash0.[6] hash0.[7] wk in
  let l = [a'; b'; c'; d'; e'; f'; g'; h'] in                                      
  elim_of_list l;
  lemma_sha256_rnds2_spec_update_is_shuffle_core hash0 wk t block;
  ()

#push-options "--z3rlimit 10"
let lemma_rnds2_spec_quad32_is_shuffle_core_x2 (abef cdgh:quad32) (wk0 wk1:word SHA2_256) (block:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256 - 1}) : Lemma
  (requires wk0 == add_mod (k0 SHA2_256).[t] (ws_opaque SHA2_256 block t) /\
            wk1 == add_mod (k0 SHA2_256).[t+1] (ws_opaque SHA2_256 block (t+1)))
  (ensures (let hash0 = make_hash abef cdgh in
            let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
            let hash2 = shuffle_core_opaque SHA2_256 block hash1 (t + 1) in
            let abef', cdgh' = sha256_rnds2_spec_update_quad32 abef cdgh wk0 in
            let abef'', cdgh'' = sha256_rnds2_spec_update_quad32 abef' cdgh' wk1 in
            hash2 == make_hash abef'' cdgh''))
  =
  let hash0 = make_hash abef cdgh in
  let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
  let hash2 = shuffle_core_opaque SHA2_256 block hash1 (t + 1) in
  let abef', cdgh' = sha256_rnds2_spec_update_quad32 abef cdgh wk0 in
  let abef'', cdgh'' = sha256_rnds2_spec_update_quad32 abef' cdgh' wk1 in
  lemma_rnds_quad32 abef cdgh wk0 block t;
  lemma_rnds_quad32 abef' cdgh' wk1 block (t+1);
  assert (equal (make_hash abef' cdgh') hash1);
  assert (equal (make_hash abef'' cdgh'') hash2);
  ()
#pop-options

let sha256_rnds2_spec_update_quad32_x2_shifts (abef cdgh:quad32) (wk0 wk1:word SHA2_256) : 
  Lemma ((let abef', cdgh' = sha256_rnds2_spec_update_quad32 abef cdgh wk0 in
          let abef'', cdgh'' = sha256_rnds2_spec_update_quad32 abef' cdgh' wk1 in
          cdgh'' == abef))
  =
  ()

let sha256_rnds2_spec_quad32_is_shuffle_core_x2 (abef cdgh wk:quad32) (block:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256 - 1}) : Lemma
  (requires wk.lo0 == vv (add_mod (k0 SHA2_256).[t]   (ws_opaque SHA2_256 block t)) /\
            wk.lo1 == vv (add_mod (k0 SHA2_256).[t+1] (ws_opaque SHA2_256 block (t+1))))
  (ensures (let hash0 = make_hash abef cdgh in
            let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
            let hash2 = shuffle_core_opaque SHA2_256 block hash1 (t + 1) in
            let abef' = sha256_rnds2_spec_quad32 cdgh abef wk in
            hash2 == make_hash abef' abef))
  =
  lemma_rnds2_spec_quad32_is_shuffle_core_x2 abef cdgh (to_uint32 wk.lo0) (to_uint32 wk.lo1) block t;
  sha256_rnds2_spec_update_quad32_x2_shifts abef cdgh (to_uint32 wk.lo0) (to_uint32 wk.lo1);
  ()

let lemma_sha256_rnds2_two_steps (abef cdgh xmm0:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires t + 1 < size_k_w SHA2_256 /\
            xmm0.lo0 == add_wrap (vv (k0 SHA2_256).[t]  ) (vv (ws_opaque SHA2_256 block t)) /\
            xmm0.lo1 == add_wrap (vv (k0 SHA2_256).[t+1]) (vv (ws_opaque SHA2_256 block (t+1))) )
  (ensures (let hash0 = make_hash abef cdgh in
            let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
            let hash2 = shuffle_core_opaque SHA2_256 block hash1 (t + 1) in
            hash2 == make_hash (sha256_rnds2_spec cdgh abef xmm0) abef))
  =  
  let hash0 = make_hash abef cdgh in
  let hash1 = shuffle_core_opaque SHA2_256 block hash0 t in
  let hash2 = shuffle_core_opaque SHA2_256 block hash1 (t+1) in
  sha256_rnds2_spec_quad32_is_shuffle_core_x2 abef cdgh xmm0 block t;
  lemma_sha256_rnds2_spec_quad32 cdgh abef xmm0;
  ()

// Top-level proof for the SHA256_rnds2 instruction
let lemma_sha256_rnds2 (abef cdgh xmm0:quad32) (t:counter) (block:block_w SHA2_256) (hash_in:hash_w SHA2_256) : Lemma
  (requires t + 1 < size_k_w SHA2_256 /\
            xmm0.lo0 == add_wrap (vv (k0 SHA2_256).[t]  ) (vv (ws_opaque SHA2_256 block t)) /\
            xmm0.lo1 == add_wrap (vv (k0 SHA2_256).[t+1]) (vv (ws_opaque SHA2_256 block (t+1))) /\ 
            make_hash abef cdgh == Spec.Loops.repeat_range_spec 0 t (shuffle_core_opaque SHA2_256 block) hash_in
            )
  (ensures make_hash (sha256_rnds2_spec cdgh abef xmm0) abef ==
           Spec.Loops.repeat_range_spec 0 (t+2) (shuffle_core_opaque SHA2_256 block) hash_in)
  =
  lemma_sha256_rnds2_two_steps abef cdgh xmm0 t block;
  Spec.Loops.lemma_repeat_range_spec 0 (t + 1) (shuffle_core_opaque SHA2_256 block) hash_in;
  Spec.Loops.lemma_repeat_range_spec 0 (t + 2) (shuffle_core_opaque SHA2_256 block) hash_in;
  ()

(* Proof work for the SHA256_msg* instructions *)

let ws_quad32 (t:counter) (block:block_w SHA2_256) : quad32 =
    if t < size_k_w SHA2_256 - 3 then
       Mkfour (vv (ws_opaque SHA2_256 block t))
              (vv (ws_opaque SHA2_256 block (t+1)))
              (vv (ws_opaque SHA2_256 block (t+2)))
              (vv (ws_opaque SHA2_256 block (t+3)))
    else 
       Mkfour 0 0 0 0

let _sigma0_quad32 (q:quad32) : quad32 =
  Mkfour (vv (_sigma0 SHA2_256 (to_uint32 q.lo0)))
         (vv (_sigma0 SHA2_256 (to_uint32 q.lo1)))
         (vv (_sigma0 SHA2_256 (to_uint32 q.hi2)))
         (vv (_sigma0 SHA2_256 (to_uint32 q.hi3)))

let _sigma1_quad32 (q:quad32) : quad32 =
  Mkfour (vv (_sigma1 SHA2_256 (to_uint32 q.lo0)))
         (vv (_sigma1 SHA2_256 (to_uint32 q.lo1)))
         (vv (_sigma1 SHA2_256 (to_uint32 q.hi2)))
         (vv (_sigma1 SHA2_256 (to_uint32 q.hi3)))

let ws_partial_def (t:counter) (block:block_w SHA2_256) : quad32 =
    if 16 <= t && t < size_k_w SHA2_256 then
       (let init = ws_quad32 (t-16) block in
        let sigma0_in = ws_quad32 (t-15) block in
        let sigma0_out = _sigma0_quad32 sigma0_in in
        add_wrap_quad32 init sigma0_out)
    else 
       Mkfour 0 0 0 0

unfold let ws_partial = make_opaque ws_partial_def

let add_mod_quad32 (q0 q1:quad32) : quad32 =
  Mkfour (vv (add_mod (to_uint32 q0.lo0) (to_uint32 q1.lo0)))
         (vv (add_mod (to_uint32 q0.lo1) (to_uint32 q1.lo1)))
         (vv (add_mod (to_uint32 q0.hi2) (to_uint32 q1.hi2)))
         (vv (add_mod (to_uint32 q0.hi3) (to_uint32 q1.hi3)))

let lemma_add_wrap_quad32_is_add_mod_quad32 (q0 q1:quad32) :
  Lemma (add_mod_quad32 q0 q1 == add_wrap_quad32 q0 q1)
  =
  FStar.Classical.forall_intro_2 lemma_add_wrap_is_add_mod;
  ()

// Top-level proof for the SHA256_msg1 instruction
let lemma_sha256_msg1 (dst src:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) /\
            dst == ws_quad32 (t-16) block /\
            src.lo0 == vv(ws_opaque SHA2_256 block (t-12)))
  (ensures sha256_msg1_spec dst src == ws_partial t block)
  =
  reveal_opaque sha256_msg1_spec_def;
  let init = ws_quad32 (t-16) block in
  let sigma0_in = ws_quad32 (t-15) block in
  let sigma0_out = _sigma0_quad32 sigma0_in in
  lemma_add_wrap_quad32_is_add_mod_quad32 init sigma0_out;
  reveal_opaque ws_partial_def;
  ()
  

let lemma_add_mod_ws_rearrangement (a b c d:UInt32.t) :
  Lemma (add_mod a (add_mod b (add_mod c d)) == add_mod (add_mod (add_mod d c) b) a)
  =
  lemma_add_mod_commutes (add_mod (add_mod d c) b) a;
  assert (add_mod (add_mod (add_mod d c) b) a == add_mod a (add_mod (add_mod d c) b));
  lemma_add_mod_commutes (add_mod d c) b;
  assert (add_mod a (add_mod (add_mod d c) b) == add_mod a (add_mod b (add_mod d c)));
  lemma_add_mod_commutes d c;
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
    (word_add_mod a (word_add_mod a (word_add_mod a t16 s0) t7) s1)

#push-options "--max_fuel 1"
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
#pop-options

let lemma_ws_computed_is_ws_opaque (b:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256}) :
  Lemma (ws_computed SHA2_256 b t == ws_opaque SHA2_256 b t)
  =
  lemma_ws_computed_is_ws b t;
  reveal_opaque ws;
  ()


let ws_computed_quad32 (t:counter{t < size_k_w SHA2_256 - 3}) (block:block_w SHA2_256) : quad32 =
       Mkfour (vv (ws_computed SHA2_256 block t))
              (vv (ws_computed SHA2_256 block (t+1)))
              (vv (ws_computed SHA2_256 block (t+2)))
              (vv (ws_computed SHA2_256 block (t+3)))

let lemma_ws_computed_is_ws_quad32 (b:block_w SHA2_256) (t:counter{t < size_k_w SHA2_256 - 3}) :
  Lemma (ws_computed_quad32 t b == ws_quad32 t b)
  =
  let w = ws_computed_quad32 t b in
  let w' = ws_quad32 t b in
  lemma_ws_computed_is_ws_opaque b t;
  lemma_ws_computed_is_ws_opaque b (t+1);
  lemma_ws_computed_is_ws_opaque b (t+2);
  lemma_ws_computed_is_ws_opaque b (t+3);  
  ()

#push-options "--z3rlimit 30"
let lemma_ws_computed_quad32 (t:counter{16 <= t /\ t < size_k_w SHA2_256 - 4}) (block:block_w SHA2_256) :
  Lemma (let t_minus_16 = ws_quad32 (t-16) block in
         let t_minus_15 = ws_quad32 (t-15) block in
         let t_minus_7 = ws_quad32 (t - 7) block in
         let t_minus_2 = ws_quad32 (t - 2) block in        
         let m1 = add_mod_quad32 t_minus_16 (_sigma0_quad32 t_minus_15) in
         let m2 = add_mod_quad32 m1 t_minus_7 in
         let m3 = add_mod_quad32 m2 (_sigma1_quad32 t_minus_2) in
         m3 == ws_computed_quad32 t block )
  =
  ()
#pop-options  

let sha256_msg1_spec_t (t:counter{t < size_k_w SHA2_256 - 1}) (block:block_w SHA2_256) : quad32 =
  let init = ws_quad32 t block in
  let next = ws_quad32 (t + 1) block in
  let msg1 = add_mod_quad32 init (_sigma0_quad32 next) in
  msg1

let lemma_sha256_msg1_spec_t_partial (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < size_k_w SHA2_256 - 3)
  (ensures ws_partial t block == sha256_msg1_spec_t (t-16) block)
  =
  reveal_opaque ws_partial_def;
  let init = ws_quad32 (t-16) block in
  let next = ws_quad32 (t-15) block in
  lemma_add_wrap_quad32_is_add_mod_quad32 init (_sigma0_quad32 next);
  ()
          
let lemma_sha256_msg1_spec_t (src1 src2:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires t < size_k_w SHA2_256 - 4 /\
            src1 == ws_quad32 t block /\
            src2.lo0 == vv (ws_opaque SHA2_256 block (t+4)))
  (ensures sha256_msg1_spec_t t block == sha256_msg1_spec src1 src2)
  =
  reveal_opaque sha256_msg1_spec_def;
  ()

#push-options "--z3rlimit 30"
let lemma_sha256_step2 (src1 src2:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) - 3 /\
            src2.hi2 == vv (ws_opaque SHA2_256 block (t-2)) /\
            src2.hi3 == vv (ws_opaque SHA2_256 block (t-1)) /\
            (let w = sha256_msg1_spec_t (t-16) block in
             let mid = ws_quad32 (t-7) block in
             src1 == add_mod_quad32 w mid))
  (ensures sha256_msg2_spec src1 src2 == ws_computed_quad32 t block)
  =
  reveal_opaque sha256_msg2_spec_def;
  let w = sha256_msg1_spec_t (t-16) block in
  let mid = ws_quad32 (t-7) block in
  let final = sha256_msg2_spec src1 src2 in
  lemma_ws_computed_is_ws_opaque block (t);
  lemma_ws_computed_is_ws_opaque block (t+1);
  ()
#pop-options

// Top-level proof for the SHA256_msg2 instruction
let lemma_sha256_msg2 (src1 src2:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < size_k_w(SHA2_256) - 3 /\
            (let step1 = ws_partial t block in
             let t_minus_7 = ws_quad32 (t-7) block in
             src1 == add_wrap_quad32 step1 t_minus_7 /\

             src2.hi2 == vv (ws_opaque SHA2_256 block (t-2)) /\
             src2.hi3 == vv (ws_opaque SHA2_256 block (t-1))))
  (ensures sha256_msg2_spec src1 src2 == ws_quad32 t block)
  =
  let step1 = ws_partial t block in
  let t_minus_7 = ws_quad32 (t-7) block in
  lemma_sha256_msg1_spec_t_partial t block;
  // ==> step1 == sha256_msg1_spec_t (t-16) block
  lemma_add_wrap_quad32_is_add_mod_quad32 step1 t_minus_7;
  lemma_sha256_step2 src1 src2 t block;
  lemma_ws_computed_is_ws_quad32 block t;
  ()

open GCM_helpers
(* Abbreviations and lemmas for the code itself *)
let k_reqs (k_seq:seq quad32) : Type0 =
  length k_seq == 64 / 4 /\
  (forall i . {:pattern (index_work_around_quad32 k_seq i)} 0 <= i /\ i < (64/4) ==> 
    (k_seq.[i]).lo0 == vv (k0 SHA2_256).[4 `op_Multiply` i] /\
    (k_seq.[i]).lo1 == vv (k0 SHA2_256).[4 `op_Multiply` i + 1] /\
    (k_seq.[i]).hi2 == vv (k0 SHA2_256).[4 `op_Multiply` i + 2] /\
    (k_seq.[i]).hi3 == vv (k0 SHA2_256).[4 `op_Multiply` i + 3])
  
let quads_to_block (qs:seq quad32) : block_w SHA2_256
  =
  let nat32_seq = Words.Seq_s.seq_four_to_seq_LE qs in
  let f (n:nat{n < 16}) : UInt32.t = to_uint32 (if n < length nat32_seq then nat32_seq.[n] else 0) in
  init 16 f

#push-options "--z3rlimit 20 --max_fuel 1"
let lemma_quads_to_block (qs:seq quad32) : Lemma
  (requires length qs == 4)
  (ensures (let block = quads_to_block qs in
            forall i . {:pattern (index_work_around_quad32 qs i)} 0 <= i /\ i < 4 ==>
              (qs.[i]).lo0 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 0)) /\
              (qs.[i]).lo1 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 1)) /\
              (qs.[i]).hi2 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 2)) /\
              (qs.[i]).hi3 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 3)) /\
              qs.[i] == ws_quad32 (4 `op_Multiply` i) block))
  =  
  reveal_opaque ws;
  ()
#pop-options

let translate_hash_update (h0 h1 a0 a1:quad32) : 
  Lemma (let h0' = add_wrap_quad32 a0 h0 in
         let h1' = add_wrap_quad32 a1 h1 in
         let h = make_hash h0 h1 in
         let a = make_hash a0 a1 in
         let h' = make_hash h0' h1' in
         let mapped = Spec.Loops.seq_map2 (fun x y -> word_add_mod SHA2_256 x y) h a in
         mapped == h')
  =
  admit()
         
unfold let shuffle_opaque = make_opaque shuffle
  
let update_block (a:hash_alg) (hash:hash_w a) (block:block_w a): Tot (hash_w a) =
  let hash_1 = shuffle_opaque a hash block in
  Spec.Loops.seq_map2 (fun x y -> word_add_mod a x y) hash hash_1

let update_lemma (src1 src2 src1' src2' h0 h1:quad32) (block:block_w SHA2_256) : Lemma
  (requires (let hash_orig = make_hash h0 h1 in
             make_hash src1 src2 == 
             Spec.Loops.repeat_range_spec 0 64 (shuffle_core_opaque SHA2_256 block) hash_orig /\
             src1' == add_wrap_quad32 src1 h0 /\
             src2' == add_wrap_quad32 src2 h1))
  (ensures (let hash_orig = make_hash h0 h1 in
            make_hash src1' src2' == update_block SHA2_256 hash_orig block))
  =
  let hash_orig = make_hash h0 h1 in
  let hash_1 = shuffle_opaque SHA2_256 hash_orig block in
  reveal_opaque shuffle;
  reveal_opaque shuffle_core;
  //assert (hash_1 == shuffle SHA2_256 hash_orig block);
  let h = make_hash src1 src2 in
  assert (shuffle_core_opaque == shuffle_core);
  //assert_norm (shuffle_core_opaque == shuffle_core);
  //let open FStar.FunctionalExtensionality in
  //assert (feq shuffle_core shuffle_core_opaque);
  //assert (FStar.FunctionalExtensionality.feq (shuffle_core_opaque SHA2_256 block) (shuffle_core SHA2_256 block));
  assert (shuffle_core_opaque SHA2_256 block == shuffle_core SHA2_256 block);
  assert (Spec.Loops.repeat_range_spec 0 64 (shuffle_core_opaque SHA2_256 block) hash_orig ==
          Spec.Loops.repeat_range_spec 0 64 (shuffle_core SHA2_256 block) hash_orig);
  assert (make_hash src1 src2 == shuffle SHA2_256 hash_orig block); 
  //assert (h == hash_1);
  //let h' = make_hash src1' src2' in
  //let u = update SHA2_256 hash_orig block in
  //assert (equal h' u);
  translate_hash_update src1 src2 h0 h1;
  admit();
  ()
            
            
  

