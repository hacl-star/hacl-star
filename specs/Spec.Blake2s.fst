module Spec.Blake2s

open FStar.Mul
open FStar.All
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq


(* Algorithm parameters *)
inline_for_extraction let size_hash_w : size_nat = 8
inline_for_extraction let size_word : size_nat = 4
inline_for_extraction let size_block_w : size_nat = 16
inline_for_extraction let size_block : size_nat = size_block_w * size_word
inline_for_extraction let max_size_hash : size_nat = 32
inline_for_extraction let rounds_in_f : size_nat = 10


(* Definition of base types *)
type working_vector = intseq U32 size_block_w
type message_block = intseq U32 size_block_w
type hash_state = intseq U32 size_hash_w
type idx = n:size_nat{n < 16}
type counter = uint64
type last_block_flag = bool

noeq type state = {
  s: hash_state;
  t: intseq U32 2;
  f: intseq U32 2;
  buf: intseq U8 size_block;
  buflen: size_t;
  outlen: size_t;
  last_node: uint8;
}


(* Constants *)
inline_for_extraction let r1 = u32 16
inline_for_extraction let r2 = u32 12
inline_for_extraction let r3 = u32 8
inline_for_extraction let r4 = u32 7

inline_for_extraction let list_init : list uint32 =
  [u32 0x6A09E667; u32 0xBB67AE85; u32 0x3C6EF372; u32 0xA54FF53A;
   u32 0x510E527F; u32 0x9B05688C; u32 0x1F83D9AB; u32 0x5BE0CD19]

let const_iv : intseq U32 8 =
  assert_norm (List.Tot.length list_init = 8);
  createL list_init

inline_for_extraction let list_sigma: list (n:size_t{size_v n < 16}) = [
  size  0; size  1; size  2; size  3; size  4; size  5; size  6; size  7;
  size  8; size  9; size 10; size 11; size 12; size 13; size 14; size 15;
  size 14; size 10; size  4; size  8; size  9; size 15; size 13; size  6;
  size  1; size 12; size  0; size  2; size 11; size  7; size  5; size  3;
  size 11; size  8; size 12; size  0; size  5; size  2; size 15; size 13;
  size 10; size 14; size  3; size  6; size  7; size  1; size  9; size  4;
  size  7; size  9; size  3; size  1; size 13; size 12; size 11; size 14;
  size  2; size  6; size  5; size 10; size  4; size  0; size 15; size  8;
  size  9; size  0; size  5; size  7; size  2; size  4; size 10; size 15;
  size 14; size  1; size 11; size 12; size  6; size  8; size  3; size 13;
  size  2; size 12; size  6; size 10; size  0; size 11; size  8; size  3;
  size  4; size 13; size  7; size  5; size 15; size 14; size  1; size  9;
  size 12; size  5; size  1; size 15; size 14; size 13; size  4; size 10;
  size  0; size  7; size  6; size  3; size  9; size  2; size  8; size 11;
  size 13; size 11; size  7; size 14; size 12; size  1; size  3; size  9;
  size  5; size  0; size 15; size  4; size  8; size  6; size  2; size 10;
  size  6; size 15; size 14; size  9; size 11; size  3; size  0; size  8;
  size 12; size  2; size 13; size  7; size  1; size  4; size 10; size  5;
  size 10; size  2; size  8; size  4; size  7; size  6; size  1; size  5;
  size 15; size 11; size  9; size 14; size  3; size 12; size 13; size 0
]

let const_sigma:lseq (n:size_t{size_v n < 16}) 160 =
  assert_norm (List.Tot.length list_sigma = 160);
  createL list_sigma


(* Functions *)
let g1 (wv: working_vector) (a:idx) (b:idx) (r:rotval U32) : Tot working_vector =
  wv.[a] <- (wv.[a] ^. wv.[b]) >>>. r

let g2 (wv:working_vector) (a:idx) (b:idx) (x:uint32) : Tot working_vector =
  wv.[a] <- (wv.[a] +. wv.[b] +. x)


val blake2_mixing : working_vector -> idx -> idx -> idx -> idx -> uint32 -> uint32 -> Tot working_vector
let blake2_mixing wv a b c d x y =
  let wv = g2 wv a b x in
  let wv = g1 wv d a r1 in
  let wv = g2 wv c d (u32 0) in
  let wv = g1 wv b c r2 in
  let wv = g2 wv a b y in
  let wv = g1 wv d a r3 in
  let wv = g2 wv c d (u32 0) in
  let wv = g1 wv b c r4 in
  wv


val blake2_round1 : working_vector -> message_block -> size_nat -> Tot working_vector
let blake2_round1 wv m i =
  let s = sub const_sigma ((i % 10) * 16) 16 in
  let wv = blake2_mixing wv 0 4  8 12 (m.[size_v s.[ 0]]) (m.[size_v s.[ 1]]) in
  let wv = blake2_mixing wv 1 5  9 13 (m.[size_v s.[ 2]]) (m.[size_v s.[ 3]]) in
  let wv = blake2_mixing wv 2 6 10 14 (m.[size_v s.[ 4]]) (m.[size_v s.[ 5]]) in
  let wv = blake2_mixing wv 3 7 11 15 (m.[size_v s.[ 6]]) (m.[size_v s.[ 7]]) in
  wv


val blake2_round2 : working_vector -> message_block -> size_nat -> Tot working_vector
let blake2_round2 wv m i =
  let s = sub const_sigma ((i % 10) * 16) 16 in
  let wv = blake2_mixing wv 0 5 10 15 (m.[size_v s.[ 8]]) (m.[size_v s.[ 9]]) in
  let wv = blake2_mixing wv 1 6 11 12 (m.[size_v s.[10]]) (m.[size_v s.[11]]) in
  let wv = blake2_mixing wv 2 7  8 13 (m.[size_v s.[12]]) (m.[size_v s.[13]]) in
  let wv = blake2_mixing wv 3 4  9 14 (m.[size_v s.[14]]) (m.[size_v s.[15]]) in
  wv


val blake2_round : message_block -> size_nat -> working_vector -> Tot working_vector
let blake2_round m i wv =
  let wv = blake2_round1 wv m i in
  let wv = blake2_round2 wv m i in
  wv


val blake2_compress1 : working_vector -> hash_state -> message_block -> uint64 -> last_block_flag -> Tot working_vector
let blake2_compress1 wv s m offset flag =
  let wv = update_sub wv 0 8 s in
  let wv = update_sub wv 8 8 const_iv in
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 32) in
  let wv_12 = wv.[12] ^. low_offset in
  let wv_13 = wv.[13] ^. high_offset in
  let wv_14 = wv.[14] ^. (u32 0xFFFFFFFF) in
  let wv = wv.[12] <- wv_12 in
  let wv = wv.[13] <- wv_13 in
  let wv = if flag then wv.[14] <- wv_14 else wv in
  wv


val blake2_compress2: working_vector -> message_block -> Tot working_vector
let blake2_compress2 wv m = repeati rounds_in_f (blake2_round m) wv


val blake2_compress3_inner: working_vector -> i:size_nat{i < 8} -> hash_state -> Tot hash_state
let blake2_compress3_inner wv i s =
  let i_plus_8 = i + 8 in
  let si_xor_wvi = logxor #U32 s.[i] wv.[i] in
  let si = logxor #U32 si_xor_wvi wv.[i_plus_8] in
  s.[i] <- si


val blake2_compress3: working_vector -> hash_state -> Tot hash_state
let blake2_compress3 wv s = repeati 8 (blake2_compress3_inner wv) s


val blake2_compress : hash_state -> message_block -> uint64 -> last_block_flag -> Tot hash_state
let blake2_compress s m offset flag =
  let wv = create 16 (u32 0) in
  let wv = blake2_compress1 wv s m offset flag in
  let wv = blake2_compress2 wv m in
  let s = blake2_compress3 wv s in
  s


// Init0
val blake2s_internal1: hash_state -> kk:size_nat{kk<=32} -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot hash_state
let blake2s_internal1 s kk nn =
  let s0 = s.[0] in
  let s0' = s0 ^. (u32 0x01010000) ^. ((u32 kk) <<. (u32 8)) ^. (u32 nn) in
  s.[0] <- s0'


// Update 1
val blake2s_internal2_inner: dd:size_nat{0 < dd /\ dd * size_block <= max_size_t} -> d:lbytes (dd * size_block) -> i:size_nat{i < dd - 1} -> hash_state -> Tot hash_state
let blake2s_internal2_inner dd d i s =
  let sub_d = (sub d (i * size_block) size_block) in
  let to_compress : intseq U32 16 = uints_from_bytes_le sub_d in
  let offset = u64 ((i + 1) * size_block) in
  blake2_compress s to_compress offset false


// Update_blocks // Update_multi
val blake2s_internal2_loop : dd:size_nat{0 < dd /\ dd * size_block <= max_size_t} -> d:lbytes (dd * size_block) -> hash_state -> Tot hash_state
let blake2s_internal2_loop dd d s = repeati (dd - 1) (blake2s_internal2_inner dd d) s


// BB. This seems odd as blake2 internal should be called when dd = 1 !!
val blake2s_internal2 : dd:size_nat{0 < dd /\ dd * size_block <= max_size_t} -> d:lbytes (dd * size_block) -> hash_state -> Tot hash_state
let blake2s_internal2 dd d s =
  if dd > 1 then
    blake2s_internal2_loop dd d s
  else s


// Update last
// We should insert the key in update1 instead ?
val blake2s_internal3 : hash_state -> dd:size_nat{0 < dd /\ dd * size_block <= max_size_t} -> d:lbytes (dd * size_block) -> ll:size_nat -> kk:size_nat{kk<=32} -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot hash_state

let blake2s_internal3 s dd d ll kk nn =
  let offset : size_nat = (dd - 1) * 16 * 4 in
  let last_block : intseq U32 16 = uints_from_bytes_le (sub d offset size_block) in
  if kk = 0 then
    blake2_compress s last_block (u64 ll) true
  else
    blake2_compress s last_block (u64 (ll + size_block)) true


val blake2s_internal_core : dd:size_nat{0 < dd /\ dd * size_block <= max_size_t} -> d:lbytes (dd * size_block) -> ll:size_nat -> kk:size_nat{kk<=32} -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lseq uint8 32)
let blake2s_internal_core dd d ll kk nn =
  let s = const_iv in
  let s = blake2s_internal1 s kk nn in
  let s = blake2s_internal2 dd d s in
  let s = blake2s_internal3 s dd d ll kk nn in
  uints_to_bytes_le s


val blake2s_internal : dd:size_nat{0 < dd /\ dd * size_block <= max_size_t} -> d:lbytes (dd * size_block) -> ll:size_nat -> kk:size_nat{kk<=32} -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)
let blake2s_internal dd d ll kk nn =
  let tmp = blake2s_internal_core dd d ll kk nn in
  sub tmp 0 nn


val blake2s : ll:size_nat{0 < ll /\ ll <= max_size_t - 2 * size_block } ->  d:lbytes ll ->  kk:size_nat{kk <= 32} -> k:lbytes kk -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)

let blake2s ll d kk k nn =
  let nblocks = ll / size_block in
  let rem = ll % size_block in
  let blocks = sub d 0 (nblocks * size_block) in
  let last = sub d (nblocks * size_block) rem in
  let key_block = create size_block (u8 0) in
  let key_block = update_sub key_block 0 kk k in
  let last_block = create size_block (u8 0) in
  let last_block = update_sub last_block 0 rem last in
  let (|nblocks, data|) : ( n:size_nat{n * size_block <= max_size_t} & lseq uint8 (n * size_block))=
    if rem = 0 then (|nblocks, blocks|)
    else (|(nblocks + 1), concat blocks last_block|)
  in

  let (|nblocks, data|)  =
    if kk = 0 then (|nblocks, data|)
    else (|(nblocks + 1), concat key_block data|)
  in
  blake2s_internal nblocks data ll kk nn
