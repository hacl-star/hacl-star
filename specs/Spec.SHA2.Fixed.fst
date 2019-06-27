module Spec.SHA2.Fixed

open FStar.Mul
open Lib.IntTypes
open Lib.FixedSequence
open Lib.ByteSequence
open Lib.LoopCombinators
module D = Spec.Hash.Definitions
module C = Spec.SHA2.Constants

(* Define the length of the constants. Also the number of scheduling rounds. *)

inline_for_extraction noextract
let size_k_w: D.sha2_alg -> Tot nat = function
  | D.SHA2_224 | D.SHA2_256 -> 64
  | D.SHA2_384 | D.SHA2_512 -> 80

inline_for_extraction noextract
let word_n: D.sha2_alg -> Tot nat = function
  | D.SHA2_224 | D.SHA2_256 -> 32
  | D.SHA2_384 | D.SHA2_512 -> 64

inline_for_extraction noextract
let v' (#a: D.sha2_alg) (x:D.word a) = match a with
  | D.SHA2_224 | D.SHA2_256 -> uint_v #U32 #SEC x
  | D.SHA2_384 | D.SHA2_512 -> uint_v #U64 #SEC x

let lanes = n:flen{n == 1 \/ n == 4 \/ n == 8}
//let wordxN (w:lanes) (a:D.sha2_alg) = vec_t (D.word_t a) w
let wordxN (w:lanes) (a:D.sha2_alg) = fseq (D.word a) w

let block    (a: D.sha2_alg) = lbytes (D.block_length a)
let hash     (a: D.sha2_alg) = lbytes (D.hash_length a)
let k_w      (w:lanes )(a: D.sha2_alg) = Lib.Sequence.lseq (wordxN w a) (size_k_w a)
let state_w  (w:lanes) (a: D.sha2_alg) = fseq (wordxN w a) (D.state_word_length a)
let block_w     (w:lanes) (a: D.sha2_alg) = fseq (wordxN w a) (D.block_word_length)
let counter = nat

inline_for_extraction noextract
type ops = {
  c0: size_t; c1: size_t; c2: size_t;
  c3: size_t; c4: size_t; c5: size_t;
  e0: size_t; e1: size_t; e2: size_t;
  e3: size_t; e4: size_t; e5: size_t;
}

(* Definition of constants used in word functions *)
inline_for_extraction noextract
let op224_256: ops = {
  c0 = 2ul; c1 = 13ul; c2 = 22ul;
  c3 = 6ul; c4 = 11ul; c5 = 25ul;
  e0 = 7ul; e1 = 18ul; e2 = 3ul;
  e3 = 17ul; e4 = 19ul; e5 = 10ul
}

inline_for_extraction noextract
let op384_512: ops = {
  c0 = 28ul; c1 = 34ul; c2 = 39ul;
  c3 = 14ul; c4 = 18ul; c5 = 41ul;
  e0 = 1ul ; e1 =  8ul; e2 =  7ul;
  e3 = 19ul; e4 = 61ul; e5 =  6ul
}

inline_for_extraction
let op0: a:D.sha2_alg -> Tot ops = function
  | D.SHA2_224 -> op224_256
  | D.SHA2_256 -> op224_256
  | D.SHA2_384 -> op384_512
  | D.SHA2_512 -> op384_512

inline_for_extraction
let ( +| ) (#w:lanes) (#a:D.sha2_alg): wordxN w a -> wordxN w a -> wordxN w a =
  match a with
  | D.SHA2_224 | D.SHA2_256 -> ( +| ) #U32 #SEC #w
  | D.SHA2_384 | D.SHA2_512 -> ( +| ) #U64 #SEC #w

inline_for_extraction
let ( ^| ) (#w:lanes) (#a:D.sha2_alg): wordxN w a -> wordxN w a -> wordxN w a =
  match a with
  | D.SHA2_224 | D.SHA2_256 -> ( ^| ) #U32 #SEC #w
  | D.SHA2_384 | D.SHA2_512 -> ( ^| ) #U64 #SEC #w


inline_for_extraction
let ( &| ) (#w:lanes) (#a:D.sha2_alg): wordxN w a -> wordxN w a -> wordxN w a =
  match a with
  | D.SHA2_224 | D.SHA2_256 -> ( &| ) #U32 #SEC #w
  | D.SHA2_384 | D.SHA2_512 -> ( &| ) #U64 #SEC #w

inline_for_extraction
let ( ~| ) (#w:lanes) (#a:D.sha2_alg): wordxN w a  -> wordxN w a =
  match a with
  | D.SHA2_224 | D.SHA2_256 -> ( ~| ) #U32 #SEC #w
  | D.SHA2_384 | D.SHA2_512 -> ( ~| ) #U64 #SEC #w

inline_for_extraction
let ( >>>| ) (#w:lanes) (#a:D.sha2_alg): wordxN w a -> rotval (D.word_t a) -> wordxN w a =
  match a with
  | D.SHA2_224 | D.SHA2_256 -> ( >>>| ) #U32 #SEC #w
  | D.SHA2_384 | D.SHA2_512 -> ( >>>| ) #U64 #SEC #w

inline_for_extraction
let ( >>| ) (#w:lanes) (#a:D.sha2_alg): wordxN w a -> shiftval (D.word_t a) ->  wordxN w a =
  match a with
  | D.SHA2_224 | D.SHA2_256 -> ( >>| ) #U32 #SEC #w
  | D.SHA2_384 | D.SHA2_512 -> ( >>| ) #U64 #SEC #w

(* Definition of the SHA2 word functions *)
inline_for_extraction
val _Ch: #w:lanes -> #a:D.sha2_alg -> wordxN w a -> wordxN w a -> wordxN w a -> wordxN w a
inline_for_extraction
let _Ch #w #a x y z =  (x &| y) ^| (~|x &| z)

inline_for_extraction
val _Maj: #w:lanes -> #a:D.sha2_alg -> wordxN w a -> wordxN w a -> wordxN w a -> wordxN w a
inline_for_extraction
let _Maj #w #a x y z = (x &| y) ^| ((x &| z) ^| (y &| z))

inline_for_extraction
val _Sigma0: #w:lanes -> #a:D.sha2_alg -> wordxN w a -> wordxN w a
inline_for_extraction
let _Sigma0 #w #a x = (x >>>| (op0 a).c0) ^| (x >>>| (op0 a).c1) ^| (x >>>| (op0 a).c2)

inline_for_extraction
val _Sigma1: #w:lanes -> #a:D.sha2_alg -> wordxN w a -> wordxN w a
inline_for_extraction
let _Sigma1 #w #a x = (x >>>| (op0 a).c3) ^| (x >>>| (op0 a).c4) ^| (x >>>| (op0 a).c5)

inline_for_extraction
val _sigma0: #w:lanes -> #a:D.sha2_alg -> wordxN w a -> wordxN w a
inline_for_extraction
let _sigma0 #w #a x = (x >>>| (op0 a).e0) ^| (x >>>| (op0 a).e1) ^| (x >>| (op0 a).e2)

inline_for_extraction
val _sigma1: #w:lanes -> #a:D.sha2_alg -> wordxN w a -> wordxN w a
inline_for_extraction
let _sigma1 #w #a x = (x >>>| (op0 a).e3) ^| (x >>>| (op0 a).e4) ^| (x >>| (op0 a).e5)

inline_for_extraction
let h0 (w:lanes) (a:D.sha2_alg) : state_w w a =
  match a with
  | D.SHA2_224 -> map (create w) (from_lseq C.h224)
  | D.SHA2_256 -> map (create w) (from_lseq C.h256)
  | D.SHA2_384 -> map (create w) (from_lseq C.h384)
  | D.SHA2_512 -> map (create w) (from_lseq C.h512)

inline_for_extraction
let k0 (w:lanes) (a:D.sha2_alg) : k_w w a =
  match a with
  | D.SHA2_224 -> Lib.Sequence.map (create w) C.k224_256
  | D.SHA2_256 -> Lib.Sequence.map (create w) C.k224_256
  | D.SHA2_384 -> Lib.Sequence.map (create w) C.k384_512
  | D.SHA2_512 -> Lib.Sequence.map (create w) C.k384_512

let ws0_inner (#w:lanes) (#a:D.sha2_alg) (b:block a) (i:nat{w * i < D.block_word_length}) : wordxN w a =
  fseq_from_bytes_be #(D.word_t a) #SEC #w (Lib.Sequence.sub b (i * w * D.word_length a) (w * D.word_length a))

let ws0 (#w:lanes) (#a:D.sha2_alg) (b:fseq (block a) w) : block_w w a  =
  let b_w = map (fseq_from_bytes_be #(D.word_t a) #SEC #(D.block_word_length)) b in
  createi D.block_word_length (fun i -> createi w (fun j -> b_w.[j].[i]))
	  (*
	  let r = i / (D.block_word_length / w) in
	  let c = i % (D.block_word_length / w) in
	  ws0_inner b.[r] c) *)
	  // NEED TO TRANSPOSE // DONE?


let ws_next_inner (#w:lanes) (#a:D.sha2_alg) (i:nat{i < D.block_word_length}) (ws:block_w w a) : block_w w a =
    let t16 = ws.[i] in
    let t15 = ws.[(i+1)%16] in
    let t7  = ws.[(i+9)%16] in
    let t2  = ws.[(i+14)%16] in
    let s1 = _sigma1 t2 in
    let s0 = _sigma0 t15 in
    ws.[i] <- s1 +| t7 +| s0 +| t16

let ws_next (#w:lanes) (#a:D.sha2_alg) (ws:block_w w a) : block_w w a =
  repeati D.block_word_length (ws_next_inner #w #a) ws


(* Core shuffling function *)
let shuffle_core (#w:lanes) (#a:D.sha2_alg)
		 (k_t:wordxN w a) (ws_t:wordxN w a)
		 (hash:state_w w a) : state_w w a =
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in
  let t1 = h0 +| _Sigma1 e0  +| _Ch e0 f0 g0 +| k_t +| ws_t in
  let t2 = _Sigma0 a0 +| _Maj a0 b0 c0 in
  let hash = hash.[0] <- t1 +| t2 in
  let hash = hash.[1] <- a0 in
  let hash = hash.[2] <- b0 in
  let hash = hash.[3] <- c0 in
  let hash = hash.[4] <- d0 +| t1 in
  let hash = hash.[5] <- e0 in
  let hash = hash.[6] <- f0 in
  let hash = hash.[7] <- g0 in
  hash

(* Full shuffling function *)
let shuffle (#w:lanes) (#a:D.sha2_alg) (ws:block_w w a) (h:state_w w a) : state_w w a =
  let h',_ =
      repeati (size_k_w a / 16)
	    (fun i (h,ws) ->
	      let k = from_lseq (Lib.Sequence.sub (k0 w a) (i*16) 16) in
	      let h' = repeati 16 (fun j h -> shuffle_core #w #a k.[j] ws.[j] h) h in
	      let ws' = ws_next ws in
	      (h',ws')) (h,ws) in
  map2 (+|) h h'

let init = h0

(* Compression function *)
let compress (#w:lanes) (#a:D.sha2_alg) (blocks:fseq (block a) w) (hash:state_w w a) : state_w w a =
  let ws = ws0 #w #a blocks in
  shuffle ws hash

let encoded_len (#a:D.sha2_alg) (total_len:nat{total_len < D.max_input_length a}) =
    uint_to_bytes_be (secret (nat_to_uint #(D.len_int_type a) #PUB (total_len * 8)))

let num_pad_blocks (a:D.sha2_alg) (len:size_nat{len < D.block_length a}) =
  let len' = len + D.len_length a + 1 in
  if len' <= D.block_length a then 1 else 2

let prepare_last (#a:D.sha2_alg) (nblocks:nat)
		 (len:size_nat{len < D.block_length a /\
			       nblocks * D.block_length a + len < D.max_input_length a})
		 (last:lbytes len):
		 block a & block a  =
    let open Lib.Sequence in
    let total_len = ((nblocks * D.block_length a) + len)  in
    let nb = num_pad_blocks a len in
    let blocks = create (2 * D.block_length a) (u8 0) in
    let blocks = update_sub blocks 0 len last in
    let blocks = blocks.[len] <- (u8 0x80) in
    let blocks = update_sub blocks ((nb * D.block_length a) - D.len_length a)
			    (D.len_length a) (encoded_len #a total_len) in
    let block0 = sub blocks 0 (D.block_length a) in
    let block1 = sub blocks (D.block_length a) (D.block_length a) in
    block0, block1


let compress_last  (#w:lanes) (#a:D.sha2_alg)
		   (nblocks:nat)
		   (len:size_nat{len < D.block_length a /\
				 nblocks * D.block_length a + len < D.max_input_length a})
  		   (last:fseq (lbytes len) w) (hash:state_w w a) : state_w w a =
    let blocks : fseq (block a & block a) w = map (prepare_last #a nblocks len) last in
    let blocks0 = map Pervasives.fst blocks in
    let blocks1 = map Pervasives.snd blocks in
    if num_pad_blocks a len = 1 then
      compress blocks0 hash
    else
      compress blocks1 (compress blocks0 hash)


let store_hash_a (i:nat{i <= 8}) = unit

let store_hash_inner (#w:lanes) (#a:D.sha2_alg) (h:fseq (fseq (D.word a) (D.state_word_length a)) w)
		     (i:nat{i < w}) (p:unit): unit & lbytes (D.word_length a * D.state_word_length a) =
    (), fseq_to_bytes_be h.[i]

let store_hash (#w:lanes) (#a:D.sha2_alg) (h:state_w w a) : lbytes (w * D.word_length a * D.state_word_length a) =
    let th = createi w (fun i -> createi (D.state_word_length a) (fun j -> h.[j].[i])) in
    let p,s = Lib.Sequence.generate_blocks (D.word_length a * D.state_word_length a) w w store_hash_a
	      (store_hash_inner #w #a h) () in
    s // NEED TO TRANSPOSE

(*
let store_hash (#w:lanes) (#a:D.sha2_alg) (h:state_w w a) : lbytes (8 * w * D.word_length a) =

    let thb = map (fun b -> fseq_to_bytes_be b) th in
    let s = repeati w (fun i h -> Lib.Sequence.concat h @| thb.[i])  in
    s // (DONE?) NEED TO TRANSPOSE
*)

let finish (#w:lanes) (#a:D.sha2_alg) (h:state_w w a) : fseq (hash a) w =
    let hb = store_hash h in
    createi w (fun i -> Lib.Sequence.sub hb (i * w * D.word_length a) (D.hash_length a))

let hash1 (a:D.sha2_alg) (input:bytes{Lib.Sequence.length input < D.max_input_length a}) : hash a =
  let nblocks = Lib.Sequence.length input / D.block_length a in
  let st = Lib.Sequence.repeat_blocks (D.block_length a) input
	   (compress #1 #a)
	   (compress_last #1 #a nblocks)
	   (init 1 a) in
  (finish #1 st <: hash a)



