module Spec.Chacha20_Vec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector

#set-options "--max_fuel 0 --z3rlimit 100"

/// Constants and Types

let size_key = 32
let size_block = 64
let size_nonce = 12

(* TODO: Remove, left here to avoid breaking implementation *)
let keylen = 32   (* in bytes *)
let blocklen = 64 (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes size_key
type block1 = lbytes size_block
type nonce = lbytes size_nonce
type counter = size_nat
type subblock = b:bytes{length b <= size_block}

// Internally, blocks are represented as 16 x 4-byte integers
let lanes = n:width{n == 1 \/ n == 4 \/ n == 8 \/ n == 16}
let uint32xN (w:lanes) = vec_t U32 w
type state (w:lanes) = lseq (uint32xN w) 16
type idx = n:size_nat{n < 16}
type shuffle (w:lanes) = state w -> state w
type blocks (w:lanes) = lbytes (w * 64)

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)


/// Specification

let line (#w:lanes) (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:state w) : state w =
  let m = m.[a] <- (m.[a] +| m.[b]) in
  let m = m.[d] <- ((m.[d] ^| m.[a]) <<<| s) in m

let quarter_round (#w:lanes) a b c d : shuffle w =
  line a b d (size 16) @
  line c d b (size 12) @
  line a b d (size 8)  @
  line c d b (size 7)

let column_round (#w:lanes) : shuffle w =
  quarter_round 0 4 8  12 @
  quarter_round 1 5 9  13 @
  quarter_round 2 6 10 14 @
  quarter_round 3 7 11 15

let diagonal_round (#w:lanes) : shuffle w =
  quarter_round 0 5 10 15 @
  quarter_round 1 6 11 12 @
  quarter_round 2 7 8  13 @
  quarter_round 3 4 9  14

let double_round (#w:lanes) : shuffle w =
  column_round @ diagonal_round (* 2 rounds *)

let rounds (#w:lanes) : shuffle w =
  repeat 10 double_round (* 20 rounds *)

let chacha20_core (#w:lanes) (s0:state w) 
		  (ctr:counter) : state w =
  let k = s0 in
  let cv = vec_load (u32 w *. u32 ctr) w in
  let k = k.[12] <- k.[12] +| cv in
  let k = rounds k in
  let k = map2 (+|) k s0 in
  k.[12] <- k.[12] +| cv

inline_for_extraction
let c0 = 0x61707865ul
inline_for_extraction
let c1 = 0x3320646eul
inline_for_extraction
let c2 = 0x79622d32ul
inline_for_extraction
let c3 = 0x6b206574ul

let chacha20_constants : lseq size_t 4 = 
  [@ inline_let]
  let l = [c0;c1;c2;c3] in
  assert_norm(List.Tot.length l == 4);
  createL l
  
let setup1 (k:key) (n:nonce) (ctr0:counter) : lseq uint32 16 =
  let st1 = create 16 (u32 0) in
  let st1 = update_sub st1 0 4 (map secret chacha20_constants) in
  let st1 = update_sub st1 4 8 (uints_from_bytes_le #U32 #SEC #8 k) in
  let st1 = st1.[12] <- u32 ctr0 in
  let st1 = update_sub st1 13 3 (uints_from_bytes_le #U32 #SEC #3 n) in
  st1

inline_for_extraction
let vec_load_i (#t:v_inttype) (w:width) (x:uint_t t SEC) = vec_load #t x w

let chacha20_init (#w:lanes) (k:key) (n:nonce) (ctr0:counter) : state w = 
  let st1 = setup1 k n ctr0 in
  let st = map (vec_load_i w) st1 in
  let c = vec_counter U32 w in
  st.[12] <- st.[12] +| c

let transpose_store_blocks (#w:lanes) (st:state w) : lseq uint32 (w * 16)  = 
  createi (w * 16) (fun i -> (vec_v st.[i % 16]).[i / 16]) 

let store_blocks (#w:lanes) (st:state w) : lseq uint32 (w * 16)  = 
  createi (w * 16) (fun i -> (vec_v st.[i / w]).[i % w]) 

let load_blocks1 (sq:lseq uint32 16) : state 1 = 
  createi 16 (fun i -> vec_load sq.[i] 1)

let load_blocks4 (sq:lseq uint32 64) : state 4 = 
  createi 16 (fun i -> vec_load4 sq.[4*i] sq.[4*i+1] sq.[4*i+2] sq.[4*i+3])

let load_blocks8 (sq:lseq uint32 128) : state 8 = 
  createi 16 (fun i -> vec_load8 sq.[8*i] sq.[8*i+1] sq.[8*i+2] sq.[8*i+3] 
			      sq.[8*4] sq.[8*i+5] sq.[8*i+6] sq.[8*i+7])

let load_blocks16 (sq:lseq uint32 256) : state 16 = 
  createi 16 (fun i -> vec_load16 sq.[16*i] sq.[16*i+1] sq.[16*i+2] sq.[16*i+3] 
			      sq.[16*4] sq.[16*i+5] sq.[16*i+6] sq.[16*i+7]
			      sq.[16*8] sq.[16*i+9] sq.[16*i+10] sq.[16*i+11] 
			      sq.[16*12] sq.[16*i+13] sq.[16*i+14] sq.[16*i+15])


let load_blocks (#w:lanes) (sq:lseq uint32 (w * 16)) : state w = 
  match w with
  | 1 -> load_blocks1 sq
  | 4 -> load_blocks4 sq
  | 8 -> load_blocks8 sq
  | 16 -> load_blocks16 sq

let transpose (#w:lanes) (st:state w) : state w = 
  load_blocks (transpose_store_blocks st)
  
let chacha20_key_block0 (#w:lanes) (k:key) (n:nonce) : Tot block1 =
  let st = chacha20_init #w k n 0 in
  let kb = transpose_store_blocks st in
  uints_to_bytes_le (sub kb 0 16)

let xor_block (#w:lanes) (k:state w) (b:blocks w) : blocks w  = 
  let iby = uints_from_bytes_le b in
  let ib = load_blocks iby in 
  let kb = transpose k in
  let ob = map2 (^|) ib kb in
  let oby = store_blocks ob in
  uints_to_bytes_le oby

let chacha20_encrypt_block (#w:lanes) (st0:state w) (incr:counter) (b:blocks w) : blocks w =
  let k = chacha20_core st0 incr in
  xor_block k b
  
let chacha20_encrypt_last
  (#w:lanes)
  (st0: state w)
  (incr: counter)
  (len: size_nat{len < w * size_block})
  (b: lbytes len) :
  Tot (lbytes len) =

  let plain = create (w * size_block) (u8 0) in
  let plain = update_sub plain 0 len b in
  let cipher = chacha20_encrypt_block st0 incr plain in
  sub cipher 0 (length b)


val chacha20_update:
    #w:lanes
  -> st0: state w
  -> msg: bytes{length msg / (w * size_block)  <= max_size_t}
  -> cipher: bytes{length cipher == length msg}
let chacha20_update #w st0 msg = 
  let cipher = msg in
  map_blocks (w * size_block) cipher
    (chacha20_encrypt_block st0)
    (chacha20_encrypt_last st0)


val chacha20encrypt_bytes:
    #w:lanes
  -> k: key
  -> n: nonce
  -> c: counter
  -> msg: bytes{length msg / (w * size_block) <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let chacha20_encrypt_bytes #w key nonce ctr0 msg =
  let st0 = chacha20_init #w key nonce ctr0 in
  chacha20_update #w st0 msg

val chacha20_decrypt_bytes:
    #w:lanes
  -> k: key
  -> n: nonce
  -> c: counter
  -> cipher: bytes{length cipher / (w * size_block) <= max_size_t}
  -> msg: bytes{length cipher == length msg}

let chacha20_decrypt_bytes #w key nonce ctr0 cipher =
  let st0 = chacha20_init #w key nonce ctr0 in
  chacha20_update #w st0 cipher
