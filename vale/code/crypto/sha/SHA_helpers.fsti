module SHA_helpers

open Prop_s
open Opaque_s
open Spec.SHA2
open Spec.Hash
open Spec.Hash.Helpers
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

// Duplicate these definitions from Spec.SHA2.fst, since we can't see it here
let block_w  (a: sha2_alg) = m:seq (word a) {length m = size_block_w}
let counter = nat
val k0 : (seq (word SHA2_256) {length k0 = 64}
 
// Hide various SHA2 definitions
val ws_opaque (a:sha2_alg) (b:block_w a) (t:counter{t < 64}): Tot (word a)
val shuffle_core_opaque (a:sha2_alg) (block:block_w a) (hash:hash_w a) (t:counter{t < 64}): Tot (hash_w a) 
val update_multi_opaque (a:hash_alg) (hash:hash_w a) (blocks:bytes_blocks a):Tot (hash_w a) (decreases (length blocks))

// Work around some limitations in Vale's support for dependent types
unfold let block256 = block_w SHA2_256
unfold let hash256 = hash_w SHA2_256
//unfold let bytes_blocks256 = bytes_blocks SHA2_256
unfold let repeat_range_vale (max:nat { max < 64}) (block:block256) (hash:hash256) =
  Spec.Loops.repeat_range 0 max (shuffle_core_opaque SHA2_256 block) hash
unfold let lemma_repeat_range_0_vale (block:block256) (hash:hash256) = 
  Spec.Loops.repeat_range_base 0 (shuffle_core_opaque SHA2_256 block) hash
unfold let update_multi_opaque_vale (hash:hash256) (blocks:bytes) : hash256 = 
  if length blocks % 64 = 0 then let b:bytes_blocks SHA2_256 = blocks in update_multi_opaque SHA2_256 hash b else hash

val make_hash_def (abef cdgh:quad32) :
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
    } ) 

unfold let make_hash = make_opaque make_hash_def

val make_ordered_hash_def (abcd efgh:quad32) :
  (hash:hash_w SHA2_256 {
         length hash == 8 /\
         hash.[0] == to_uint32 abcd.lo0 /\
         hash.[1] == to_uint32 abcd.lo1 /\
         hash.[2] == to_uint32 abcd.hi2 /\
         hash.[3] == to_uint32 abcd.hi3 /\
         hash.[4] == to_uint32 efgh.lo0 /\
         hash.[5] == to_uint32 efgh.lo1 /\
         hash.[6] == to_uint32 efgh.hi2 /\
         hash.[7] == to_uint32 efgh.hi3      
   })
   
unfold let make_ordered_hash = make_opaque make_ordered_hash_def

// Top-level proof for the SHA256_rnds2 instruction
val lemma_sha256_rnds2 (abef cdgh xmm0:quad32) (t:counter) (block:block_w SHA2_256) (hash_in:hash_w SHA2_256) : Lemma
  (requires t + 1 < 64 /\
            xmm0.lo0 == add_wrap (vv (k0 SHA2_256).[t]  ) (vv (ws_opaque SHA2_256 block t)) /\
            xmm0.lo1 == add_wrap (vv (k0 SHA2_256).[t+1]) (vv (ws_opaque SHA2_256 block (t+1))) /\ 
            make_hash abef cdgh == Spec.Loops.repeat_range_spec 0 t (shuffle_core_opaque SHA2_256 block) hash_in
            )
  (ensures make_hash (sha256_rnds2_spec cdgh abef xmm0) abef ==
           Spec.Loops.repeat_range_spec 0 (t+2) (shuffle_core_opaque SHA2_256 block) hash_in)

(* Proof work for the SHA256_msg* instructions *)
let ws_quad32 (t:counter) (block:block_w SHA2_256) : quad32 =
    if t < 64 - 3 then
       Mkfour (vv (ws_opaque SHA2_256 block t))
              (vv (ws_opaque SHA2_256 block (t+1)))
              (vv (ws_opaque SHA2_256 block (t+2)))
              (vv (ws_opaque SHA2_256 block (t+3)))
    else 
       Mkfour 0 0 0 0


val ws_partial_def (t:counter) (block:block_w SHA2_256) : quad32
unfold let ws_partial = make_opaque ws_partial_def

// Top-level proof for the SHA256_msg1 instruction
val lemma_sha256_msg1 (dst src:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < 64 /\
            dst == ws_quad32 (t-16) block /\
            src.lo0 == vv(ws_opaque SHA2_256 block (t-12)))
  (ensures sha256_msg1_spec dst src == ws_partial t block)

  
// Top-level proof for the SHA256_msg2 instruction
val lemma_sha256_msg2 (src1 src2:quad32) (t:counter) (block:block_w SHA2_256) : Lemma
  (requires 16 <= t /\ t < 64 - 3 /\
            (let step1 = ws_partial t block in
             let t_minus_7 = ws_quad32 (t-7) block in
             src1 == add_wrap_quad32 step1 t_minus_7 /\

             src2.hi2 == vv (ws_opaque SHA2_256 block (t-2)) /\
             src2.hi3 == vv (ws_opaque SHA2_256 block (t-1))))
  (ensures sha256_msg2_spec src1 src2 == ws_quad32 t block)

open Workarounds

(* Abbreviations and lemmas for the code itself *)
let k_reqs (k_seq:seq quad32) : prop0 =
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

val lemma_quads_to_block (qs:seq quad32) : Lemma
  (requires length qs == 4)
  (ensures (let block = quads_to_block qs in
            forall i . {:pattern (index_work_around_quad32 qs i)} 0 <= i /\ i < 4 ==>
              (qs.[i]).lo0 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 0)) /\
              (qs.[i]).lo1 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 1)) /\
              (qs.[i]).hi2 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 2)) /\
              (qs.[i]).hi3 == vv (ws_opaque SHA2_256 block (4 `op_Multiply` i + 3)) /\
              qs.[i] == ws_quad32 (4 `op_Multiply` i) block))
         
val update_block (hash:hash256) (block:block256): Tot (hash256)

val update_lemma (src1 src2 src1' src2' h0 h1:quad32) (block:block_w SHA2_256) : Lemma
  (requires (let hash_orig = make_hash h0 h1 in
             make_hash src1 src2 == 
             Spec.Loops.repeat_range_spec 0 64 (shuffle_core_opaque SHA2_256 block) hash_orig /\
             src1' == add_wrap_quad32 src1 h0 /\
             src2' == add_wrap_quad32 src2 h1))
  (ensures (let hash_orig = make_hash h0 h1 in
            make_hash src1' src2' == update_block hash_orig block))


let rec update_multi_quads (s:seq quad32) (hash_orig:hash256) : Tot (hash256) (decreases (length s))
  =
  if length s < 4 then
    hash_orig
  else
    let prefix, qs = split s (length s - 4) in
    let h_prefix = update_multi_quads prefix hash_orig in
    let hash = update_block h_prefix (quads_to_block qs) in
    hash

let seq_nat8_to_seq_U8 (b:seq nat8) : (b':seq UInt8.t) =
  init (length b) (fun (i:nat { i < length b }) -> let x:UInt8.t = UInt8.uint_to_t (index b i) in x)


val lemma_update_multi_equiv_vale (hash hash':hash_w SHA2_256) (quads:seq quad32) (r_quads:seq quad32)
  (nat8s:seq nat8) (blocks:seq UInt8.t) :
  Lemma (requires length quads % 4 == 0 /\
                  r_quads == reverse_bytes_quad32_seq quads /\
                  nat8s == le_seq_quad32_to_bytes quads /\
                  blocks == seq_nat8_to_seq_U8 nat8s /\
                  hash' == update_multi_quads r_quads hash)        
        (ensures 
           length blocks % 64 == 0 /\
           hash' == update_multi_opaque_vale hash blocks)
        (decreases (length quads)) 


val lemma_update_multi_quads (s:seq quad32) (hash_orig:hash_w SHA2_256) (bound:nat) : Lemma
    (requires bound + 4 <= length s)
    (ensures (let prefix_LE = slice s 0 bound in
              let prefix_BE = reverse_bytes_quad32_seq prefix_LE in
              let h_prefix = update_multi_quads prefix_BE hash_orig in
              let block_quads_LE = slice s bound (bound + 4) in
              let block_quads_BE = reverse_bytes_quad32_seq block_quads_LE in
              let input_LE = slice s 0 (bound+4) in
              let input_BE = reverse_bytes_quad32_seq input_LE in
              let h = update_block h_prefix (quads_to_block block_quads_BE) in
              h == update_multi_quads input_BE hash_orig))

let le_bytes_to_hash (b:seq nat8) : hash_w SHA2_256 =
  if length b <> 32 then   
     (let f (n:nat{n < 8}) : UInt32.t = to_uint32 0 in
     init 8 f)
  else (
     let open Words.Seq_s in
     Spec.Loops.seq_map to_uint32 (seq_nat8_to_seq_nat32_LE b)
  )

val lemma_hash_to_bytes (s:seq quad32) : Lemma
  (requires length s == 2)
  (ensures make_ordered_hash s.[0] s.[1] == le_bytes_to_hash (le_seq_quad32_to_bytes s))
