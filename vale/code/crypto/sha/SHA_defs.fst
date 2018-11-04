module SHA_defs

open Prop_s
open Types_s
open Words_s
open Workarounds
open Spec.Hash.Helpers
open Spec.SHA2
open FStar.Seq
open FStar.UInt32  // Interop with UInt-based SHA spec

unfold
let (.[]) = FStar.Seq.index

// Define these specific converters here, so that F* only reasons about 
// the correctness of the conversion once, rather that at every call site
let vv (u:UInt32.t) : nat32 = v u
let to_uint32 (n:nat32) : UInt32.t = uint_to_t n

(* Abbreviations and lemmas for the code itself *)
let k_reqs (k_seq:seq quad32) : prop0 =
  length k_seq == 64 / 4 /\
  (forall i . {:pattern (index_work_around_quad32 k_seq i)} 0 <= i /\ i < (64/4) ==> 
    (k_seq.[i]).lo0 == vv (k0 SHA2_256).[4 `op_Multiply` i] /\
    (k_seq.[i]).lo1 == vv (k0 SHA2_256).[4 `op_Multiply` i + 1] /\
    (k_seq.[i]).hi2 == vv (k0 SHA2_256).[4 `op_Multiply` i + 2] /\
    (k_seq.[i]).hi3 == vv (k0 SHA2_256).[4 `op_Multiply` i + 3])

let seq_nat8_to_seq_U8 (b:seq nat8) : (b':seq UInt8.t) =
  init (length b) (fun (i:nat { i < length b }) -> let x:UInt8.t = UInt8.uint_to_t (index b i) in x)

let le_bytes_to_hash (b:seq nat8) : hash_w SHA2_256 =
  if length b <> 32 then   
     (let f (n:nat{n < 8}) : UInt32.t = to_uint32 0 in
     init 8 f)
  else (
     let open Words.Seq_s in
     Spec.Loops.seq_map to_uint32 (seq_nat8_to_seq_nat32_LE b)
  )

open Spec.Hash
unfold let update_multi_256 (hash:hash_w SHA2_256) (blocks:bytes) : Pure (hash_w SHA2_256)
  (requires length blocks % 64 = 0)
  (ensures fun _ -> True)
  = 
  update_multi SHA2_256 hash blocks
