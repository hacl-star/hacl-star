module Spec.Blake2

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

#set-options "--z3rlimit 25 --max_fuel 0"

type alg =
  | Blake2S
  | Blake2B

inline_for_extraction
let wt (a:alg) =
  match a with
  | Blake2S -> U32
  | Blake2B -> U64

inline_for_extraction
let rounds (a:alg) =
  match a with
  | Blake2S -> 10
  | Blake2B -> 12


(* Algorithm parameters *)
inline_for_extraction let size_hash_w : size_nat = 8
inline_for_extraction let size_block_w : size_nat = 16
inline_for_extraction let size_word (a:alg) : size_nat = numbytes (wt a)
inline_for_extraction let size_block (a:alg) : size_nat = size_block_w * (size_word a)
inline_for_extraction let max_size_hash : size_nat = 32

inline_for_extraction let size_const_iv : size_nat = 8
inline_for_extraction let size_const_sigma : size_nat = 160


(* Definition of base types *)
inline_for_extraction
let limb_inttype (a:alg) =
  match (wt a) with
  | U32 -> U64
  | U64 -> U128

type word_t (a:alg) = uint_t (wt a)
type limb_t (a:alg) : Type0 = uint_t (limb_inttype a)

inline_for_extraction
let to_word (a:alg) (x:size_nat) : word_t a =
  match (wt a) with
  | U32 -> u32 x
  | U64 -> u64 x

inline_for_extraction
let to_limb (a:alg) (x:size_nat) : limb_t a =
  match (wt a) with
  | U32 -> u64 x
  | U64 -> u128 x

inline_for_extraction
let limb_to_word (a:alg) (x:limb_t a) : word_t a =
  match (wt a) with
  | U32 -> to_u32 #U64 x
  | U64 -> to_u64 #U128 x



inline_for_extraction
let rTable_list_S : l:list (rotval U32){List.Tot.length l = 4} =
  [
    size 16; size 12; size 8; size 7
  ]

inline_for_extraction
let rTable_list_B: l:list (rotval U64){List.Tot.length l = 4} =
  [
    size 32; size 24; size 16; size 63
  ]

inline_for_extraction
let rTable (a:alg) : lseq (rotval (wt a)) 4 =
  match a with
  | Blake2S -> of_list rTable_list_S
  | Blake2B -> of_list rTable_list_B


inline_for_extraction let list_iv_S: l:list uint32{List.Tot.length l = 8} =
  [@inline_let]
  let l =
  [u32 0x6A09E667; u32 0xBB67AE85; u32 0x3C6EF372; u32 0xA54FF53A;
   u32 0x510E527F; u32 0x9B05688C; u32 0x1F83D9AB; u32 0x5BE0CD19] in
  assert_norm(List.Tot.length l = 8);
  l

inline_for_extraction let list_iv_B: l:list uint64{List.Tot.length l = 8}  =
  [@inline_let]
  let l = [
    u64 0x6A09E667F3BCC908; u64 0xBB67AE8584CAA73B;
    u64 0x3C6EF372FE94F82B; u64 0xA54FF53A5F1D36F1;
    u64 0x510E527FADE682D1; u64 0x9B05688C2B3E6C1F;
    u64 0x1F83D9ABFB41BD6B; u64 0x5BE0CD19137E2179]
  in
  assert_norm(List.Tot.length l = 8);
  l

inline_for_extraction
let ivTable (a:alg) : lseq (word_t a) 8 =
  match a with
  | Blake2S -> of_list list_iv_S
  | Blake2B -> of_list list_iv_B

type sigma_elt_t = n:size_t{size_v n < 16}
type list_sigma_t = l:list sigma_elt_t{List.Tot.length l = 160}

inline_for_extraction let list_sigma: list_sigma_t =
  [@inline_let]
  let l = [
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
    size 15; size 11; size  9; size 14; size  3; size 12; size 13; size  0]
  in
  assert_norm(List.Tot.length l = 160);
  l

let const_sigma:lseq sigma_elt_t size_const_sigma =
  assert_norm (List.Tot.length list_sigma = size_const_sigma);
  of_list list_sigma


inline_for_extraction
let const_FF (a:alg) : word_t a =
  match (wt a) with
  | U32 -> u32 0xFFFFFFFF
  | U64 -> u64 0xFFFFFFFFFFFFFFFF


(* Algorithms types *)
type working_vector_s (a:alg) = lseq (word_t a) size_block_w
type message_block_ws (a:alg) = lseq (word_t a) size_block_w
type message_block_s (a:alg) = lseq uint8 (size_block a)
type hash_state_s (a:alg) = lseq (word_t a) size_hash_w
type idx_t = n:size_nat{n < 16}
type last_block_flag = bool


(* Functions *)
let g1 (a:alg) (wv:working_vector_s a) (i:idx_t) (j:idx_t) (r:rotval (wt a)) : Tot (working_vector_s a) =
  wv.[i] <- (wv.[i] ^. wv.[j]) >>>. r

let g2 (a:alg) (wv:working_vector_s a) (i:idx_t) (j:idx_t) (x:word_t a) : Tot (working_vector_s a) =
  wv.[i] <- (wv.[i] +. wv.[j] +. x)

val blake2_mixing:
  a:alg
  -> ws:working_vector_s a
  -> idx_t
  -> idx_t
  -> idx_t
  -> idx_t
  -> word_t a
  -> word_t a ->
  Tot (working_vector_s a)

let blake2_mixing al wv a b c d x y =
  let wv = g2 al wv a b x in
  let wv = g1 al wv d a (rTable al).[0] in
  let wv = g2 al wv c d (to_word al 0) in
  let wv = g1 al wv b c (rTable al).[1] in
  let wv = g2 al wv a b y in
  let wv = g1 al wv d a (rTable al).[2] in
  let wv = g2 al wv c d (to_word al 0) in
  let wv = g1 al wv b c (rTable al).[3] in
  wv


val blake2_round1:
    a:alg
  -> wv:working_vector_s a
  -> m:message_block_ws a
  -> i:size_nat ->
  Tot (working_vector_s a)

let blake2_round1 a wv m i =
  let s = sub const_sigma ((i % 10) * 16) 16 in
  let wv = blake2_mixing a wv 0 4  8 12 (m.[size_v s.[ 0]]) (m.[size_v s.[ 1]]) in
  let wv = blake2_mixing a wv 1 5  9 13 (m.[size_v s.[ 2]]) (m.[size_v s.[ 3]]) in
  let wv = blake2_mixing a wv 2 6 10 14 (m.[size_v s.[ 4]]) (m.[size_v s.[ 5]]) in
  let wv = blake2_mixing a wv 3 7 11 15 (m.[size_v s.[ 6]]) (m.[size_v s.[ 7]]) in
  wv


val blake2_round2:
    a:alg
  -> wv:working_vector_s a
  -> m:message_block_ws a
  -> i:size_nat ->
  Tot (working_vector_s a)

let blake2_round2 a wv m i =
  let s = sub const_sigma ((i % 10) * 16) 16 in
  let wv = blake2_mixing a wv 0 5 10 15 (m.[size_v s.[ 8]]) (m.[size_v s.[ 9]]) in
  let wv = blake2_mixing a wv 1 6 11 12 (m.[size_v s.[10]]) (m.[size_v s.[11]]) in
  let wv = blake2_mixing a wv 2 7  8 13 (m.[size_v s.[12]]) (m.[size_v s.[13]]) in
  let wv = blake2_mixing a wv 3 4  9 14 (m.[size_v s.[14]]) (m.[size_v s.[15]]) in
  wv


val blake2_round:
    a:alg
  -> m:message_block_ws a
  -> i:size_nat
  -> wv:working_vector_s a ->
  Tot (working_vector_s a)

let blake2_round a m i wv =
  let wv = blake2_round1 a wv m i in
  let wv = blake2_round2 a wv m i in
  wv


val blake2_compress1:
  a:alg
  -> wv:working_vector_s a
  -> s:hash_state_s a
  -> m:message_block_ws a
  -> offset:limb_t a
  -> flag:last_block_flag ->
  Tot (working_vector_s a)

let blake2_compress1 a wv s m offset flag =
  let wv = update_sub wv 0 8 s in
  let wv = update_sub wv 8 8 (ivTable a) in
  let low_offset = limb_to_word a offset in
  let high_offset = limb_to_word a (shift_right #(limb_inttype a) offset (size (bits (wt a)))) in
  let wv_12 = wv.[12] ^. low_offset in
  let wv_13 = wv.[13] ^. high_offset in
  let wv_14 = wv.[14] ^. (const_FF a) in
  let wv = wv.[12] <- wv_12 in
  let wv = wv.[13] <- wv_13 in
  let wv = if flag then wv.[14] <- wv_14 else wv in
  wv


val blake2_compress2:
    a:alg
  -> wv:working_vector_s a
  -> m:message_block_ws a ->
  Tot (working_vector_s a)

let blake2_compress2 a wv m = repeati (rounds a) (blake2_round a m) wv


val blake2_compress3_inner:
  a:alg
  -> ws:working_vector_s a
  -> i:size_nat{i < 8}
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_compress3_inner a wv i s =
  let i_plus_8 = i + 8 in
  let si_xor_wvi = logxor #(wt a) s.[i] wv.[i] in
  let si = logxor #(wt a) si_xor_wvi wv.[i_plus_8] in
  s.[i] <- si


val blake2_compress3:
  a:alg
  -> ws:working_vector_s a
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_compress3 a wv s = repeati 8 (blake2_compress3_inner a wv) s


val blake2_compress:
    a:alg
  -> s:hash_state_s a
  -> m:message_block_ws a
  -> offset:limb_t a
  -> last_block_flag ->
  Tot (hash_state_s a)

let blake2_compress a s m offset flag =
  let wv = create 16 (to_word a 0) in
  let wv = blake2_compress1 a wv s m offset flag in
  let wv = blake2_compress2 a wv m in
  let s = blake2_compress3 a wv s in
  s

val blake2_update_block:
    a:alg
  -> dd_prev:size_nat{(dd_prev + 1) * (size_block a) <= max_size_t}
  -> d:message_block_s a
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_update_block a dd_prev d s =
  let to_compress : lseq (word_t a) 16 = uints_from_bytes_le #(wt a) #16 d in
  let offset = to_limb a ((dd_prev + 1) * (size_block a)) in
  blake2_compress a s to_compress offset false


val blake2_init_iv: a:alg -> Tot (hash_state_s a)
let blake2_init_iv a = (ivTable a)


val blake2_init_hash:
    a:alg
  -> s:hash_state_s a
  -> kk:size_nat{kk <= 32}
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (hash_state_s a)

let blake2_init_hash a s kk nn =
  let s0 = s.[0] in
  let s0' = s0 ^. (to_word a 0x01010000) ^. ((to_word a kk) <<. (size 8)) ^. (to_word a nn) in
  s.[0] <- s0'


val blake2_init:
    a:alg
  -> kk:size_nat{kk <= 32}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (hash_state_s a)

let blake2_init a kk k nn =
  let s = blake2_init_iv a in
  let s = blake2_init_hash a s kk nn in
  if kk = 0 then s
  else begin
    let key_block = create (size_block a) (u8 0) in
    let key_block = update_sub key_block 0 kk k in
    blake2_update_block a 0 key_block s end


val blake2_update_multi_iteration:
  a:alg
  -> dd_prev:size_nat
  -> dd:size_nat{(dd + dd_prev) * (size_block a) <= max_size_t}
  -> d:lbytes (dd * (size_block a))
  -> i:size_nat{i + 1 <= dd}
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_update_multi_iteration a dd_prev dd d i s =
  let block = (sub d (i * (size_block a)) (size_block a)) in
  blake2_update_block a (dd_prev + i) block s


val blake2_update_multi:
    a:alg
  -> dd_prev:size_nat
  -> dd:size_nat{(dd + dd_prev) * (size_block a) <= max_size_t}
  -> d:lbytes (dd * (size_block a))
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_update_multi a dd_prev dd d s =
  repeati dd (blake2_update_multi_iteration a dd_prev dd d) s


val blake2_update_last_block:
    a:alg
  -> ll:size_nat{ll + (size_block a) <= max_size_t}
  -> last_block:lbytes (size_block a)
  -> flag_key:bool
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_update_last_block a ll last_block fk s =
  let last_block : lseq (word_t a) 16 = uints_from_bytes_le #(wt a) last_block in
  if not fk then
    blake2_compress a s last_block (to_limb a ll) true
  else
    blake2_compress a s last_block (to_limb a (ll + (size_block a))) true


val blake2_update_last:
    a:alg
  -> ll:size_nat{ll + (size_block a) <= max_size_t}
  -> len:size_nat{len <= (size_block a)}
  -> last:lbytes len
  -> flag_key:bool
  -> s:hash_state_s a ->
  Tot (hash_state_s a)

let blake2_update_last a ll len last fk s =
  let last_block = create (size_block a) (u8 0) in
  let last_block = update_sub last_block 0 len last in
  blake2_update_last_block a ll last_block fk s


val blake2_update_last_empty: a:alg -> s:hash_state_s a -> Tot (hash_state_s a)
let blake2_update_last_empty a st =
  let data = create (size_block a) (u8 0) in
  blake2_update_last a 0 (size_block a) data false st


val blake2_finish:
    a:alg
  -> s:hash_state_s a
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2_finish a s nn =
  let full = uints_to_bytes_le s in
  sub full 0 nn


val blake2:
    a:alg
  -> ll:size_nat{ll + 2 * (size_block a) <= max_size_t} // This could be relaxed
  -> d:lbytes ll
  -> kk:size_nat{kk <= 32}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2 a ll d kk k nn =
  let fk = if kk = 0 then false else true in
  let rem = ll % (size_block a) in
  let nblocks = ll / (size_block a) in
  let blocks = sub d 0 (nblocks * (size_block a)) in
  let last = sub d (nblocks * (size_block a)) rem in
  let s = blake2_init a kk k nn in
  let s =
    if ll = 0 && kk = 0 then blake2_update_last_empty a s
    else begin
      let nprev = if kk = 0 then 0 else 1 in
      let s = blake2_update_multi a nprev nblocks blocks s in
      blake2_update_last a ll rem last fk s end in
  blake2_finish a s nn


inline_for_extraction
let blake2s ll d kk k n = blake2 Blake2S ll d kk k n

inline_for_extraction
let blake2b ll d kk k n = blake2 Blake2B ll d kk k n
