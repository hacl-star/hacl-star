module Spec.Blake2b

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.All
open Lib.RawIntTypes

(* Constants *)
let size_word = 64
let size_block_w = 16
let size_word = 8
let size_block : nat = size_block_w * size_word

let rounds_in_f = 12

let r1 = u32 32
let r2 = u32 24
let r3 = u32 16
let r4 = u32 63

let init_list = List.Tot.map u64
  [0x6A09E667F3BCC908; 0xBB67AE8584CAA73B;
   0x3C6EF372FE94F82B; 0xA54FF53A5F1D36F1;
   0x510E527FADE682D1; 0x9B05688C2B3E6C1F;
   0x1F83D9ABFB41BD6B; 0x5BE0CD19137E2179]
let init_vector : intseq U64 8 = assert_norm (List.Tot.length init_list = 8) ; createL init_list
let sigma_list : list (n:nat{n<16}) =
  [0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15;
   14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3;
   11;  8; 12;  0;  5;  2; 15; 13; 10; 14;  3;  6;  7;  1;  9;  4;
   7;  9;  3;  1; 13; 12; 11; 14;  2;  6;  5; 10;  4;  0; 15;  8;
   9;  0;  5;  7;  2;  4; 10; 15; 14;  1; 11; 12;  6;  8;  3; 13;
   2; 12;  6; 10;  0; 11;  8;  3;  4; 13;  7;  5; 15; 14;  1;  9;
   12;  5;  1; 15; 14; 13;  4; 10;  0;  7;  6;  3;  9;  2;  8; 11;
   13; 11;  7; 14; 12;  1;  3;  9;  5;  0; 15;  4;  8;  6;  2; 10;
   6; 15; 14;  9; 11;  3;  0;  8; 12;  2; 13;  7;  1;  4; 10;  5;
   10;  2;  8;  4;  7;  6;  1;  5; 15; 11;  9; 14;  3; 12; 13;  0]
let sigma:lseq (n:nat{n < 16}) 160 = assert_norm (List.Tot.length sigma_list = 160) ; createL sigma_list

type working_vector = intseq U64 16
type message_block = intseq U64 16
type hash_state = intseq U64 8
type idx = n:size_nat{n < 16}
type counter = uint64
type last_block_flag = bool

let g1 (v: working_vector) (a:idx) (b:idx) (r:rotval U64) : Tot working_vector =
  v.[a] <- (v.[a] ^. v.[b]) >>>. r

let g2 (v:working_vector) (a:idx) (b:idx) (x:uint64) : Tot working_vector =
  v.[a] <- (v.[a] +. v.[b] +. x)

val blake2_mixing : working_vector -> idx -> idx -> idx -> idx -> uint64 -> uint64 -> Tot working_vector

let blake2_mixing v a b c d x y =
  let v = g2 v a b x in
  let v = g1 v d a r1 in
  let v = g2 v c d (u64 0) in
  let v = g1 v b c r2 in
  let v = g2 v a b y in
  let v = g1 v d a r3 in
  let v = g2 v c d (u64 0) in
  let v = g1 v b c r4 in
  v

val blake2_compress : hash_state -> message_block -> uint128 -> last_block_flag -> Tot hash_state

let blake2_compress h m offset f =
  let v = create 16 (u64 0) in
  let v = update_slice v 0 8 h in
  let v = update_slice v 8 16 init_vector in
  let low_offset = to_u64 #U128 offset in
  let high_offset = to_u64 #U128 (offset >>. u32 size_word) in
  let v = v.[12] <- v.[12] ^. low_offset in
  let v = v.[13] <- v.[13] ^. high_offset in
  let v = if f then v.[14] <- v.[14] ^. (u64 0xFFFFFFFFFFFFFFFF) else v in
  let v = repeati rounds_in_f
    (fun i v ->
      let s = sub sigma ((i % 10) * 16) 16 in
      let v = blake2_mixing v 0 4  8 12 (m.[s.[ 0]]) (m.[s.[ 1]]) in
      let v = blake2_mixing v 1 5  9 13 (m.[s.[ 2]]) (m.[s.[ 3]]) in
      let v = blake2_mixing v 2 6 10 14 (m.[s.[ 4]]) (m.[s.[ 5]]) in
      let v = blake2_mixing v 3 7 11 15 (m.[s.[ 6]]) (m.[s.[ 7]]) in
      let v = blake2_mixing v 0 5 10 15 (m.[s.[ 8]]) (m.[s.[ 9]]) in
      let v = blake2_mixing v 1 6 11 12 (m.[s.[10]]) (m.[s.[11]]) in
      let v = blake2_mixing v 2 7  8 13 (m.[s.[12]]) (m.[s.[13]]) in
      let v = blake2_mixing v 3 4  9 14 (m.[s.[14]]) (m.[s.[15]]) in
      v
    ) v
  in
  let h = repeati 8
    (fun i h ->
      h.[i] <- h.[i] ^. v.[i] ^. v.[i+8]
    ) h
  in
  h

val blake2b_internal : dd:size_nat{0 < dd /\ dd * size_block <= max_size_t}  -> d:lbytes (dd * size_block) -> ll:size_nat -> kk:size_nat{kk<=64} -> nn:size_nat{1 <= nn /\ nn <= 64} -> Tot (lbytes nn)

let blake2b_internal dd d ll kk nn =
  let h = init_vector in
  let h = h.[0] <- h.[0] ^. (u64 0x01010000) ^. ((u64 kk) <<. (u32 8)) ^. (u64 nn) in
  let h = if dd > 1 then
    repeati (dd -1)
      (fun i h ->
	let to_compress : intseq U64 16 =
	  uints_from_bytes_le (sub d (i*size_block) size_block)
	in
	blake2_compress h to_compress (u128 ((i+1)*size_block)) false
      ) h else h
  in
  let offset : size_nat = (dd-1)*size_block in
  let last_block : intseq U64 16 = uints_from_bytes_le (sub d offset size_block) in
  let h = if kk = 0 then
    blake2_compress h last_block (u128  ll) true
    else
    blake2_compress h last_block (u128 (ll + size_block)) true
  in
  sub (uints_to_bytes_le h) 0 nn

val blake2b : ll:size_nat{0 < ll /\ ll <= max_size_t - 2 * size_block } ->  d:lbytes ll ->  kk:size_nat{kk<=64} -> k:lbytes kk -> nn:size_nat{1 <= nn /\ nn <= 64} -> Tot (lbytes nn)

let blake2b
  ll (* size of d in bytes *)
  d (* data to hash *)
  kk (* size of key in bytes *)
  k (* key *)
  nn (* size of resulting hash in bytes *) =
  let data_blocks : size_nat = ((ll - 1) / size_block) + 1 in
  let padded_data_length : size_nat = data_blocks * size_block in
  let padded_data = create padded_data_length (u8 0) in
  let padded_data : lbytes (data_blocks * size_block) = update_slice padded_data 0 ll d in
  if kk = 0 then
     blake2b_internal data_blocks padded_data ll kk nn
  else
     let padded_key = create size_block (u8 0) in
     let padded_key = update_slice padded_key 0 kk k in
     let data_length : size_nat = size_block + padded_data_length in
     let data = create data_length (u8 0) in
     let data = update_slice data 0 size_block padded_key in
     let data = update_slice data size_block data_length padded_data in
     blake2b_internal (data_blocks+1) data ll kk nn
