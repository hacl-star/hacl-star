module Hacl.Spec.Chacha20.Vec

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.IntVector
module Scalar = Spec.Chacha20

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

/// Constants and Types

let size_key = 32
let size_block = 64
let size_nonce = 12

type key = lbytes size_key
type block1 = lbytes size_block
type nonce = lbytes size_nonce
type counter = size_nat
type subblock = b:bytes{length b <= size_block}

// Internally, blocks are represented as 16 x 4-byte integers
let lanes = n:width{n == 1 \/ n == 4 \/ n == 8}
inline_for_extraction
let uint32xN (w:lanes) = vec_t U32 w
type state (w:lanes) = lseq (uint32xN w) 16
type idx = n:size_nat{n < 16}
type shuffle (w:lanes) = state w -> state w
type blocks (w:lanes) = lbytes (w * 64)

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)


/// Specification

let transpose_state (#w:lanes) (st:state w) : lseq (lseq uint32 16) w  =
  createi w (fun i ->
    let x : lseq uint32 16 = create16
      (vec_v st.[0]).[i] (vec_v st.[1]).[i] (vec_v st.[2]).[i] (vec_v st.[3]).[i]
      (vec_v st.[4]).[i] (vec_v st.[5]).[i] (vec_v st.[6]).[i] (vec_v st.[7]).[i]
      (vec_v st.[8]).[i] (vec_v st.[9]).[i] (vec_v st.[10]).[i] (vec_v st.[11]).[i]
      (vec_v st.[12]).[i] (vec_v st.[13]).[i] (vec_v st.[14]).[i] (vec_v st.[15]).[i] in
    x)


let line (#w:lanes) (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:state w) : state w =
  let m = m.[a] <- m.[a] +| m.[b] in
  let m = m.[d] <- (m.[d] ^| m.[a]) <<<| s in
  m

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

let rounds (#w:lanes) (m:state w) : state w =
  double_round (double_round (
  double_round (double_round (
  double_round (double_round (
  double_round (double_round (
  double_round (double_round m)))))))))

let sum_state (#w:lanes) (st1:state w) (st2:state w) : state w =
  map2 (+|) st1 st2

let add_counter (#w:lanes) (ctr:counter{w * ctr <= max_size_t}) (st:state w) : state w =
  let cv = vec_load (u32 w *! u32 ctr) w in
  st.[12] <- st.[12] +| cv

let chacha20_core (#w:lanes) (ctr:counter{w * ctr <= max_size_t}) (s0:state w) : state w =
  let k = add_counter ctr s0 in
  let k = rounds k in
  let k = sum_state k s0 in
  add_counter ctr k

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
  Scalar.setup k n ctr0 (create 16 (u32 0))

inline_for_extraction
let vec_load_i (#t:v_inttype) (w:width) (x:uint_t t SEC) = vec_load #t x w

let chacha20_init (#w:lanes) (k:key) (n:nonce) (ctr0:counter) : state w =
  let st1 = setup1 k n ctr0 in
  let st = map (vec_load_i w) st1 in
  let c = vec_counter U32 w in
  st.[12] <- st.[12] +| c

let transpose1 (st:state 1) : state 1 = st

inline_for_extraction
let transpose4x4 (vs:uint32xN 4 & uint32xN 4 & uint32xN 4 & uint32xN 4)
		 : uint32xN 4 & uint32xN 4 & uint32xN 4 & uint32xN 4 =
  let (v0,v1,v2,v3) = vs in
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v0'' = vec_interleave_low_n 2 v0' v2' in
  let v1'' = vec_interleave_high_n 2 v0' v2' in
  let v2'' = vec_interleave_low_n 2 v1' v3' in
  let v3'' = vec_interleave_high_n 2 v1' v3' in
  (v0'',v1'',v2'',v3'')

let transpose4 (st:state 4) : state 4 =
  let (v0,v1,v2,v3) = transpose4x4 (st.[0],st.[1],st.[2],st.[3]) in
  let (v4,v5,v6,v7) = transpose4x4 (st.[4],st.[5],st.[6],st.[7]) in
  let (v8,v9,v10,v11) = transpose4x4 (st.[8],st.[9],st.[10],st.[11]) in
  let (v12,v13,v14,v15) = transpose4x4 (st.[12],st.[13],st.[14],st.[15]) in
  create16 v0 v4 v8 v12 v1 v5 v9 v13 v2 v6 v10 v14 v3 v7 v11 v15

inline_for_extraction
let transpose8x8 (vs:uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8)
		 : uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 & uint32xN 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = vs in
  let v0' = vec_interleave_low v0 v1 in
  let v1' = vec_interleave_high v0 v1 in
  let v2' = vec_interleave_low v2 v3 in
  let v3' = vec_interleave_high v2 v3 in
  let v4' = vec_interleave_low v4 v5 in
  let v5' = vec_interleave_high v4 v5 in
  let v6' = vec_interleave_low v6 v7 in
  let v7' = vec_interleave_high v6 v7 in
  let v0'' = vec_interleave_low_n 4 v0' v2' in
  let v1'' = vec_interleave_high_n 4 v0' v2' in
  let v2'' = vec_interleave_low_n 4 v1' v3' in
  let v3'' = vec_interleave_high_n 4 v1' v3' in
  let v4'' = vec_interleave_low_n 4 v4' v6' in
  let v5'' = vec_interleave_high_n 4 v4' v6' in
  let v6'' = vec_interleave_low_n 4 v5' v7' in
  let v7'' = vec_interleave_high_n 4 v5' v7' in
  let v0''' = vec_interleave_low_n 2 v0'' v4'' in
  let v1''' = vec_interleave_high_n 2 v0'' v4'' in
  let v2''' = vec_interleave_low_n 2 v1'' v5'' in
  let v3''' = vec_interleave_high_n 2 v1'' v5'' in
  let v4''' = vec_interleave_low_n 2 v2'' v6'' in
  let v5''' = vec_interleave_high_n 2 v2'' v6'' in
  let v6''' = vec_interleave_low_n 2 v3'' v7'' in
  let v7''' = vec_interleave_high_n 2 v3'' v7'' in
  (v0''',v2''',v4''',v6''',v1''',v3''',v5''',v7''')

let transpose8 (st:state 8) : state 8 =
  let (v0,v1,v2,v3,v4,v5,v6,v7) = transpose8x8 (st.[0],st.[1],st.[2],st.[3],st.[4],st.[5],st.[6],st.[7]) in
  let (v8,v9,v10,v11,v12,v13,v14,v15) = transpose8x8 (st.[8],st.[9],st.[10],st.[11],st.[12],st.[13],st.[14],st.[15]) in
  create16 v0 v8 v1 v9 v2 v10 v3 v11 v4 v12 v5 v13 v6 v14 v7 v15

let transpose (#w:lanes) (st:state w) : state w =
  match w with
  | 1 -> transpose1 st
  | 4 -> transpose4 st
  | 8 -> transpose8 st

// let store_block0 (#w:lanes) (st:state w) : Tot block1 =
//   let bl = create 64 (u8 0) in
//   repeati (16 / w)
//     (fun i bl -> update_sub bl (i * w * 4) (w * 4) (vec_to_bytes_le st.[i])) bl

// let chacha20_key_block0 (#w:lanes) (k:key) (n:nonce) : Tot block1 =
//   let st0 = chacha20_init #w k n 0 in
//   let k = chacha20_core 0 st0 in
//   store_block0 k

let xor_block_f (#w:lanes) (k:state w) (i:nat{i < 16}) (b:lbytes (w * 4)) : lbytes (w * 4) =
  let x = vec_from_bytes_le U32 w b in
  let y = x ^| k.[i] in
  vec_to_bytes_le y

let xor_block (#w:lanes) (k:state w) (b:blocks w) : blocks w  =
  map_blocks_multi (w * 4) 16 16 b (xor_block_f #w k)

val chacha20_encrypt_block:
    #w: lanes
  -> st0: state w
  -> incr: counter{incr * w <= max_size_t}
  -> b: blocks w ->
  Tot (blocks w)
let chacha20_encrypt_block #w st0 incr b =
  let k = chacha20_core incr st0 in
  let k = transpose k in
  xor_block k b

val chacha20_encrypt_last:
    #w: lanes
  -> st0: state w
  -> incr: counter{incr * w <= max_size_t}
  -> len: size_nat{len < w * size_block}
  -> b: lbytes len ->
  Tot (lbytes len)
let chacha20_encrypt_last #w st0 incr len b =
  let plain = create (w * size_block) (u8 0) in
  let plain = update_sub plain 0 len b in
  let cipher = chacha20_encrypt_block st0 incr plain in
  sub cipher 0 len

val chacha20_update:
    #w:lanes
  -> st0: state w
  -> msg: bytes{length msg <= max_size_t}
  -> cipher: bytes{length cipher == length msg}
let chacha20_update #w st0 msg =
  let cipher = msg in
  map_blocks (w * size_block) cipher
    (chacha20_encrypt_block st0)
    (chacha20_encrypt_last st0)

val chacha20_encrypt_bytes:
    #w:lanes
  -> k: key
  -> n: nonce
  -> c: counter
  -> msg: bytes{length msg <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let chacha20_encrypt_bytes #w key nonce ctr0 msg =
  let st0 = chacha20_init #w key nonce ctr0 in
  chacha20_update #w st0 msg

val chacha20_decrypt_bytes:
    #w:lanes
  -> k: key
  -> n: nonce
  -> c: counter
  -> cipher: bytes{length cipher <= max_size_t}
  -> msg: bytes{length cipher == length msg}

let chacha20_decrypt_bytes #w key nonce ctr0 cipher =
  let st0 = chacha20_init #w key nonce ctr0 in
  chacha20_update #w st0 cipher
