module Spec.SHA2.New

module C = Spec.SHA2.Constants
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

type sha2_alg = 
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512

(* Define the length of the constants. Also the number of scheduling rounds. *)

let size_k_w: sha2_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 64
  | SHA2_384 | SHA2_512 -> 80


let wt: sha2_alg -> inttype = function
  | SHA2_224 | SHA2_256 -> U32
  | SHA2_384 | SHA2_512 -> U64


let size_hash_final_w: sha2_alg -> Tot nat = function
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8

let size_hash (a:sha2_alg) = size_hash_final_w a `op_Multiply` (numbytes (wt a))


let word a = uint_t (wt a)

let size_block_w = 16
let size_block (a:sha2_alg) = (numbytes (wt a)) `op_Multiply` size_block_w
let size_len_8 (a:sha2_alg) = (numbytes (wt a)) `op_Multiply` 2
let max_input_8 (a:sha2_alg) = ((bits (wt a)) `op_Multiply` 2) - 3
let size_hash_w = 8
let hash_w (a:sha2_alg) = lseq (word a) size_hash_w

let k_w      (a: sha2_alg) = m:lseq (word a) (size_k_w a)
let block_w  (a: sha2_alg) = m:lseq (word a) (size_block_w)

let counter = nat


let op0: a:sha2_alg -> (lseq (rotval (wt a)) 12) = function
  | SHA2_224 -> C.ops_224_256
  | SHA2_256 -> C.ops_224_256
  | SHA2_384 -> C.ops_384_512
  | SHA2_512 -> C.ops_384_512


(* Definition of the SHA2 word functions *)

val _Ch: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)

let _Ch a x y z = (x &. y) ^. ((~. x) &. z)


val _Maj: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)

let _Maj a x y z = (x &. y) ^. ((x &. z) ^. (y &. z))


val _Sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)

let _Sigma0 a x = (x >>>. (op0 a).[0]) ^. ((x >>>. (op0 a).[1]) ^. (x >>>. (op0 a).[2]))


val _Sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)

let _Sigma1 a x = (x >>>. (op0 a).[3]) ^. ((x >>>. (op0 a).[4]) ^. (x >>>. (op0 a).[5]))


val _sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)

let _sigma0 a x = (x >>>. (op0 a).[6]) ^. ((x >>>. (op0 a).[7]) ^. (x >>>. (op0 a).[8]))


val _sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)

let _sigma1 a x = (x >>>. (op0 a).[9]) ^. ((x >>>. (op0 a).[10]) ^. (x >>>. (op0 a).[11]))

let h0: a:sha2_alg -> Tot (m:hash_w a) = function
  | SHA2_224 -> C.h224
  | SHA2_256 -> C.h256
  | SHA2_384 -> C.h384
  | SHA2_512 -> C.h512

let k0: a:sha2_alg -> Tot (m:lseq (word a) (size_k_w a)) = function
  | SHA2_224 -> C.k224_256
  | SHA2_256 -> C.k224_256
  | SHA2_384 -> C.k384_512
  | SHA2_512 -> C.k384_512

(* Scheduling function *)
let rec ws (a:sha2_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
  if t < size_block_w then b.[t]
  else
    let t16 = ws a b (t - 16) in
    let t15 = ws a b (t - 15) in
    let t7  = ws a b (t - 7) in
    let t2  = ws a b (t - 2) in

    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    s1 +. t7 +. s0 +. t16

(* Core shuffling function *)
let shuffle_core (a:sha2_alg) (block:block_w a) (t:counter{t < size_k_w a}) (hash:hash_w a) : Tot (hash_w a) =
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  let t1 = h0 +. (_Sigma1 a e0) +. (_Ch a e0 f0 g0) +. (k0 a).[t] +. (ws a block t) in
  let t2 = (_Sigma0 a a0) +. (_Maj a a0 b0 c0) in

  let l = [ t1 +. t2; a0; b0; c0; d0 +. t1; e0; f0; g0 ] in
  assert_norm(List.length l = 8);
  of_list l


(* Full shuffling function *)
let shuffle (a:sha2_alg) (hash:hash_w a) (block:block_w a): Tot (hash_w a) =
  repeat_range 0 (size_k_w a) (shuffle_core a block) hash

let init = h0

(* Compression function *)
let update (a:sha2_alg) (block:lbytes (size_block a)) (hash:hash_w a) : Tot (hash_w a) =
  let block_w = uints_from_bytes_be #(wt a) block in
  let hash_1 = shuffle a hash block_w in
  map2 ( +. ) hash hash_1


#set-options "--max_fuel 0 --max_ifuel 0"

let padlen (a:sha2_alg) (len:nat) : 
	   Tot (n:size_nat{n < size_block a /\ (len + n + 1 + size_len_8 a) % size_block a = 0}) =
  (size_block a - ((len + size_len_8 a + 1) % size_block a)) % size_block a

let padded_length (a:sha2_alg) (len:nat) = len + padlen a len + 1 + size_len_8 a

let pad (a:sha2_alg)
        (len:nat{len < max_input_8 a /\ 
	       padded_length a len  <= max_size_t}):
        Tot (b:bytes{(len + length b) % size_block a = 0 /\
		     length b < size_block a + size_block a})
=
  let open FStar.Mul in
  let firstbyte: lseq uint8 1 = create 1 (u8 0x80) in
  let zeros : lseq uint8 (padlen a len) = create (padlen a len) (u8 0) in
  let len_bits = len * 8 in
  let encodedlen : lseq uint8 (size_len_8 a) = nat_to_bytes_be (size_len_8 a) (len * 8) in
  (firstbyte @| zeros @| encodedlen)

#set-options "--z3rlimit  100 --max_ifuel 2"
let update_last (a:sha2_alg) (total_len:nat{total_len < max_input_8 a /\ padded_length a total_len <= max_size_t})
		(len:size_nat{len == total_len % size_block a}) 
		(last:lbytes len) (hash:hash_w a) : Tot (hash_w a) = 
  let p = pad a total_len in
  let m = last @| (to_lseq p) in
  if length m = size_block a then
    update a m hash 
  else (
    let m0 = sub m 0 (size_block a) in
    let m1 = sub m (size_block a) (size_block a) in
    update a m1 (update a m0 hash) 
  )
  
let finish (a:sha2_alg) (hashw:hash_w a): Tot (hash:lbytes (size_hash a)) =
  let hash_final_w = sub hashw 0 (size_hash_final_w a) in
  uints_to_bytes_be #(wt a) hash_final_w
  

let sha2 (a:sha2_alg) 
         (text:bytes{length text < max_input_8 a /\ 
		     padded_length a (length text) <= max_size_t}) 
         :  Tot (lbytes (size_hash a)) =
    let hash_w = repeat_blocks (size_block a) text 
      (fun i -> update a)
      (fun i -> update_last a (length text))
      (init a) in
    finish a hash_w
