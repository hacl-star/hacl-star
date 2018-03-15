module Spec.Blake2s

open FStar.Mul
open FStar.All
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq


(* Constants *)
inline_for_extraction let word_size : size_nat = 32
inline_for_extraction let words_block_size : size_nat = 16
inline_for_extraction let bytes_in_word : size_nat = 4
inline_for_extraction let bytes_in_block : size_nat = words_block_size * bytes_in_word

inline_for_extraction let rounds_in_f : size_nat = 10
inline_for_extraction let block_bytes : size_nat = 64

inline_for_extraction let r1 = u32 16
inline_for_extraction let r2 = u32 12
inline_for_extraction let r3 = u32 8
inline_for_extraction let r4 = u32 7

inline_for_extraction let init_list : list uint32 =
  [u32 0x6A09E667; u32 0xBB67AE85; u32 0x3C6EF372; u32 0xA54FF53A;
   u32 0x510E527F; u32 0x9B05688C; u32 0x1F83D9AB; u32 0x5BE0CD19]

let init_vector : intseq U32 8 =
  assert_norm (List.Tot.length init_list = 8);
  createL init_list

inline_for_extraction let sigma_list_size : list (n:size_t{size_v n<16}) =
  [size 0; size  1; size  2; size  3; size  4; size  5; size  6; size  7; size  8; size  9; size 10; size 11; size 12; size 13; size 14; size 15; size
   14; size 10; size  4; size  8; size  9; size 15; size 13; size  6; size  1; size 12; size  0; size  2; size 11; size  7; size  5; size  3; size
   11; size  8; size 12; size  0; size  5; size  2; size 15; size 13; size 10; size 14; size  3; size  6; size  7; size  1; size  9; size  4; size
   7; size  9; size  3; size  1; size 13; size 12; size 11; size 14; size  2; size  6; size  5; size 10; size  4; size  0; size 15; size  8; size
   9; size  0; size  5; size  7; size  2; size  4; size 10; size 15; size 14; size  1; size 11; size 12; size  6; size  8; size  3; size 13; size
   2; size 12; size  6; size 10; size  0; size 11; size  8; size  3; size  4; size 13; size  7; size  5; size 15; size 14; size  1; size  9; size
   12; size  5; size  1; size 15; size 14; size 13; size  4; size 10; size  0; size  7; size  6; size  3; size  9; size  2; size  8; size 11; size
   13; size 11; size  7; size 14; size 12; size  1; size  3; size  9; size  5; size  0; size 15; size  4; size  8; size  6; size  2; size 10; size
   6; size 15; size 14; size  9; size 11; size  3; size  0; size  8; size 12; size  2; size 13; size  7; size  1; size  4; size 10; size  5; size
   10; size  2; size  8; size  4; size  7; size  6; size  1; size  5; size 15; size 11; size  9; size 14; size  3; size 12; size 13; size 0]

val size_v_sigma_list: s:size_t{size_v s<16} -> Tot (n:size_nat{n<16 /\ (uint_v #SIZE s == n)})
let size_v_sigma_list s = size_v s

inline_for_extraction let sigma_list : list (n:size_nat{n<16}) = List.Tot.map size_v_sigma_list sigma_list_size

let sigma:lseq (n:size_nat{n < 16}) 160 =
  assert_norm (List.Tot.length sigma_list = 160);
  createL sigma_list

(* Definition of base types *)
type working_vector = intseq U32 16
type message_block = intseq U32 16
type hash_state = intseq U32 8
type idx = n:size_nat{n < 16}
type counter = uint64
type last_block_flag = bool

(* Functions *)
let g1 (v: working_vector) (a:idx) (b:idx) (r:rotval U32) : Tot working_vector =
  v.[a] <- (v.[a] ^. v.[b]) >>>. r

let g2 (v:working_vector) (a:idx) (b:idx) (x:uint32) : Tot working_vector =
  v.[a] <- (v.[a] +. v.[b] +. x)


val blake2_mixing : working_vector -> idx -> idx -> idx -> idx -> uint32 -> uint32 -> Tot working_vector
let blake2_mixing v a b c d x y =
  let v = g2 v a b x in
  let v = g1 v d a r1 in
  let v = g2 v c d (u32 0) in
  let v = g1 v b c r2 in
  let v = g2 v a b y in
  let v = g1 v d a r3 in
  let v = g2 v c d (u32 0) in
  let v = g1 v b c r4 in
  v


val blake2_round1 : working_vector -> message_block -> size_nat -> Tot working_vector
let blake2_round1 v m i =
  let s = sub sigma ((i % 10) * 16) 16 in
  let v = blake2_mixing v 0 4  8 12 (m.[s.[ 0]]) (m.[s.[ 1]]) in
  let v = blake2_mixing v 1 5  9 13 (m.[s.[ 2]]) (m.[s.[ 3]]) in
  let v = blake2_mixing v 2 6 10 14 (m.[s.[ 4]]) (m.[s.[ 5]]) in
  let v = blake2_mixing v 3 7 11 15 (m.[s.[ 6]]) (m.[s.[ 7]]) in
  v

val blake2_round2 : working_vector -> message_block -> size_nat -> Tot working_vector
let blake2_round2 v m i =
  let s = sub sigma ((i % 10) * 16) 16 in
  let v = blake2_mixing v 0 5 10 15 (m.[s.[ 8]]) (m.[s.[ 9]]) in
  let v = blake2_mixing v 1 6 11 12 (m.[s.[10]]) (m.[s.[11]]) in
  let v = blake2_mixing v 2 7  8 13 (m.[s.[12]]) (m.[s.[13]]) in
  let v = blake2_mixing v 3 4  9 14 (m.[s.[14]]) (m.[s.[15]]) in
  v

val blake2_round : working_vector -> message_block -> size_nat -> Tot working_vector
let blake2_round v m i =
  let v = blake2_round1 v m i in
  let v = blake2_round2 v m i in
  v

val blake2_compress1 : working_vector -> hash_state -> message_block -> uint64 -> last_block_flag -> Tot working_vector
let blake2_compress1 v h m offset flag =
  let v = update_sub v 0 8 h in
  let v = update_sub v 8 8 init_vector in
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 word_size) in
  let v = v.[12] <- v.[12] ^. low_offset in
  let v = v.[13] <- v.[13] ^. high_offset in
  let v = if flag then v.[14] <- v.[14] ^. (u32 0xFFFFFFFF) else v in
  v

val blake2_compress2: working_vector -> hash_state -> message_block -> Tot hash_state
let blake2_compress2 v h m =
  let v = repeati rounds_in_f (fun i v -> blake2_round v m i) v in
  let h = repeati 8
    (fun i h ->
      h.[i] <- h.[i] ^. v.[i] ^. v.[i+8]
    ) h
  in
  h

val blake2_compress : hash_state -> message_block -> uint64 -> last_block_flag -> Tot hash_state
let blake2_compress h m offset flag =
  let v = create 16 (u32 0) in
  let v = blake2_compress1 v h m offset flag in
  let h = blake2_compress2 v h m in
  h

val blake2s_internal : dd:size_nat{0 < dd /\ dd * bytes_in_block <= max_size_t}  -> d:lbytes (dd * bytes_in_block) -> ll:size_nat -> kk:size_nat{kk<=32} -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)

let blake2s_internal dd d ll kk nn =
  let h = init_vector in
  let h = h.[0] <- h.[0] ^. (u32 0x01010000) ^. ((u32 kk) <<. (u32 8)) ^. (u32 nn) in
  let h =
    if dd > 1 then
    repeati (dd -1) (fun i h ->
	   let to_compress : intseq U32 16 =
	   uints_from_bytes_le (sub d (i*bytes_in_block) bytes_in_block) in
	   blake2_compress h to_compress (u64 ((i+1)*block_bytes)) false
    ) h else h
  in
  let offset : size_nat = (dd-1)*16*4 in
  let last_block : intseq U32 16 = uints_from_bytes_le (sub d offset bytes_in_block) in
  let h =
    if kk = 0 then
      blake2_compress h last_block (u64  ll) true
    else
      blake2_compress h last_block (u64 (ll + block_bytes)) true
  in
  sub (uints_to_bytes_le h) 0 nn

val blake2s : ll:size_nat{0 < ll /\ ll <= max_size_t - 2 * bytes_in_block } ->  d:lbytes ll ->  kk:size_nat{kk<=32} -> k:lbytes kk -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)

let blake2s ll d kk k nn =
  let data_blocks : size_nat = ((ll - 1) / bytes_in_block) + 1 in
  let padded_data_length : size_nat = data_blocks * bytes_in_block in
  let padded_data = create padded_data_length (u8 0) in
  let padded_data : lbytes (data_blocks * bytes_in_block) = update_slice padded_data 0 ll d in
  if kk = 0 then
    blake2s_internal data_blocks padded_data ll kk nn
  else
    let padded_key = create bytes_in_block (u8 0) in
    let padded_key = update_slice padded_key 0 kk k in
    let data_length : size_nat = bytes_in_block + padded_data_length in
    let data = create data_length (u8 0) in
    let data = update_slice data 0 bytes_in_block padded_key in
    let data = update_slice data bytes_in_block data_length padded_data in
    blake2s_internal (data_blocks+1) data ll kk nn
