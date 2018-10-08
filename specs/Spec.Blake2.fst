module Spec.Blake2

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


noeq type parameters =
  | MkParameters:
    wt:inttype{wt = U32 \/ wt = U64} ->
    rounds:size_nat ->
    rTable:lseq (rotval wt) 4 ->
    ivTable:lseq (uint_t wt) 8 ->
    parameters


(* Algorithm parameters *)
inline_for_extraction let size_hash_w : size_nat = 8
inline_for_extraction let size_block_w : size_nat = 16
inline_for_extraction let size_word (p:parameters) : size_nat = numbytes p.wt
inline_for_extraction let size_block (p:parameters) : size_nat = size_block_w * (size_word p)
inline_for_extraction let max_size_hash : size_nat = 32

inline_for_extraction let size_const_iv : size_nat = 8
inline_for_extraction let size_const_sigma : size_nat = 160


(* Definition of base types *)
inline_for_extraction
let limb_inttype (p:parameters) =
  match p.wt with
  | U32 -> U64
  | U64 -> U128

type word_t (p:parameters) = uint_t p.wt
type limb_t (p:parameters) : Type0 = uint_t (limb_inttype p)

let to_word (p:parameters) (x:size_nat) : word_t p =
  match p.wt with
  | U32 -> u32 x
  | U64 -> u64 x

let to_limb (p:parameters) (x:size_nat) : limb_t p =
  match p.wt with
  | U32 -> u64 x
  | U64 -> u128 x

let limb_to_word (p:parameters) (x:limb_t p) : word_t p =
  match p.wt with
  | U32 -> to_u32 #U64 x
  | U64 -> to_u64 #U128 x


type working_vector_s (p:parameters) = lseq (word_t p) size_block_w
type message_block_ws (p:parameters) = lseq (word_t p) size_block_w
type message_block_s (p:parameters) = lseq uint8 (size_block p)
type hash_state_s (p:parameters) = lseq (word_t p) size_hash_w
type idx_t = n:size_nat{n < 16}
type last_block_flag = bool


inline_for_extraction
let const_FF (p:parameters) : word_t p =
  match p.wt with
  | U32 -> u32 0xFFFFFFFF
  | U64 -> u64 0xFFFFFFFFFFFFFFFF


type list_sigma_elt_t = n:size_t{size_v n < 16}
type list_sigma_t = l:list list_sigma_elt_t{List.Tot.length l <= max_size_t}
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
  assert_norm(List.Tot.length l <= max_size_t);
  l

let const_sigma:lseq (n:size_t{size_v n < 16}) size_const_sigma =
  assert_norm (List.Tot.length list_sigma = size_const_sigma);
  of_list list_sigma


(* Functions *)
let g1 (p:parameters) (wv:working_vector_s p) (a:idx_t) (b:idx_t) (r:rotval p.wt) : Tot (working_vector_s p) =
  wv.[a] <- (wv.[a] ^. wv.[b]) >>>. r

let g2 (p:parameters) (wv:working_vector_s p) (a:idx_t) (b:idx_t) (x:word_t p) : Tot (working_vector_s p) =
  wv.[a] <- (wv.[a] +. wv.[b] +. x)

val blake2_mixing:
  p:parameters
  -> ws:working_vector_s p
  -> idx_t
  -> idx_t
  -> idx_t
  -> idx_t
  -> word_t p
  -> word_t p ->
  Tot (working_vector_s p)

let blake2_mixing p wv a b c d x y =
  let wv = g2 p wv a b x in
  let wv = g1 p wv d a p.rTable.[0] in
  let wv = g2 p wv c d (to_word p 0) in
  let wv = g1 p wv b c p.rTable.[1] in
  let wv = g2 p wv a b y in
  let wv = g1 p wv d a p.rTable.[2] in
  let wv = g2 p wv c d (to_word p 0) in
  let wv = g1 p wv b c p.rTable.[3] in
  wv


val blake2_round1:
    p:parameters
  -> wv:working_vector_s p
  -> m:message_block_ws p
  -> i:size_nat ->
  Tot (working_vector_s p)

let blake2_round1 p wv m i =
  let s = sub const_sigma ((i % 10) * 16) 16 in
  let wv = blake2_mixing p wv 0 4  8 12 (m.[size_v s.[ 0]]) (m.[size_v s.[ 1]]) in
  let wv = blake2_mixing p wv 1 5  9 13 (m.[size_v s.[ 2]]) (m.[size_v s.[ 3]]) in
  let wv = blake2_mixing p wv 2 6 10 14 (m.[size_v s.[ 4]]) (m.[size_v s.[ 5]]) in
  let wv = blake2_mixing p wv 3 7 11 15 (m.[size_v s.[ 6]]) (m.[size_v s.[ 7]]) in
  wv


val blake2_round2:
    p:parameters
  -> wv:working_vector_s p
  -> m:message_block_ws p
  -> i:size_nat ->
  Tot (working_vector_s p)

let blake2_round2 p wv m i =
  let s = sub const_sigma ((i % 10) * 16) 16 in
  let wv = blake2_mixing p wv 0 5 10 15 (m.[size_v s.[ 8]]) (m.[size_v s.[ 9]]) in
  let wv = blake2_mixing p wv 1 6 11 12 (m.[size_v s.[10]]) (m.[size_v s.[11]]) in
  let wv = blake2_mixing p wv 2 7  8 13 (m.[size_v s.[12]]) (m.[size_v s.[13]]) in
  let wv = blake2_mixing p wv 3 4  9 14 (m.[size_v s.[14]]) (m.[size_v s.[15]]) in
  wv


val blake2_round:
    p:parameters
  -> m:message_block_ws p
  -> i:size_nat
  -> wv:working_vector_s p ->
  Tot (working_vector_s p)

let blake2_round p m i wv =
  let wv = blake2_round1 p wv m i in
  let wv = blake2_round2 p wv m i in
  wv


val blake2_compress1:
  p:parameters
  -> wv:working_vector_s p
  -> s:hash_state_s p
  -> m:message_block_ws p
  -> offset:limb_t p
  -> flag:last_block_flag ->
  Tot (working_vector_s p)

let blake2_compress1 p wv s m offset flag =
  let wv = update_sub wv 0 8 s in
  let wv = update_sub wv 8 8 p.ivTable in
  let low_offset = limb_to_word p offset in
  let high_offset = limb_to_word p (shift_right #(limb_inttype p) offset (size (bits p.wt))) in
  let wv_12 = wv.[12] ^. low_offset in
  let wv_13 = wv.[13] ^. high_offset in
  let wv_14 = wv.[14] ^. (const_FF p) in
  let wv = wv.[12] <- wv_12 in
  let wv = wv.[13] <- wv_13 in
  let wv = if flag then wv.[14] <- wv_14 else wv in
  wv


val blake2_compress2:
    p:parameters
  -> wv:working_vector_s p
  -> m:message_block_ws p ->
  Tot (working_vector_s p)

let blake2_compress2 p wv m = repeati p.rounds (blake2_round p m) wv


val blake2_compress3_inner:
  p:parameters
  -> ws:working_vector_s p
  -> i:size_nat{i < 8}
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2_compress3_inner p wv i s =
  let i_plus_8 = i + 8 in
  let si_xor_wvi = logxor #p.wt s.[i] wv.[i] in
  let si = logxor #p.wt si_xor_wvi wv.[i_plus_8] in
  s.[i] <- si


val blake2_compress3:
  p:parameters
  -> ws:working_vector_s p
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2_compress3 p wv s = repeati 8 (blake2_compress3_inner p wv) s


val blake2_compress:
    p:parameters
  -> s:hash_state_s p
  -> m:message_block_ws p
  -> offset:limb_t p
  -> last_block_flag ->
  Tot (hash_state_s p)

let blake2_compress p s m offset flag =
  let wv = create 16 (to_word p 0) in
  let wv = blake2_compress1 p wv s m offset flag in
  let wv = blake2_compress2 p wv m in
  let s = blake2_compress3 p wv s in
  s

val blake2s_update_block:
    p:parameters
  -> dd_prev:size_nat{(dd_prev + 1) * (size_block p) <= max_size_t}
  -> d:message_block_s p
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2s_update_block p dd_prev d s =
//  assert (length d == 16 * 4);
  let to_compress : lseq (word_t p) 16 = uints_from_bytes_le #p.wt #16 d in
  let offset = to_limb p ((dd_prev + 1) * (size_block p)) in
  blake2_compress p s to_compress offset false


val blake2s_init_iv: p:parameters -> Tot (hash_state_s p)
let blake2s_init_iv p = p.ivTable


val blake2s_init_hash:
    p:parameters
  -> s:hash_state_s p
  -> kk:size_nat{kk <= 32}
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (hash_state_s p)

let blake2s_init_hash p s kk nn =
  let s0 = s.[0] in
  let s0' = s0 ^. (to_word p 0x01010000) ^. ((to_word p kk) <<. (size 8)) ^. (to_word p nn) in
  s.[0] <- s0'


val blake2s_init:
    p:parameters
  -> kk:size_nat{kk <= 32}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (hash_state_s p)

let blake2s_init p kk k nn =
  let s = blake2s_init_iv p in
  let s = blake2s_init_hash p s kk nn in
  if kk = 0 then s
  else begin
    let key_block = create (size_block p) (u8 0) in
    let key_block = update_sub key_block 0 kk k in
    blake2s_update_block p 0 key_block s end


val blake2s_update_multi_iteration:
  p:parameters
  -> dd_prev:size_nat
  -> dd:size_nat{(dd + dd_prev) * (size_block p) <= max_size_t}
  -> d:lbytes (dd * (size_block p))
  -> i:size_nat{i + 1 <= dd}
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2s_update_multi_iteration p dd_prev dd d i s =
  let block = (sub d (i * (size_block p)) (size_block p)) in
  blake2s_update_block p (dd_prev + i) block s


val blake2s_update_multi:
    p:parameters
  -> dd_prev:size_nat
  -> dd:size_nat{(dd + dd_prev) * (size_block p) <= max_size_t}
  -> d:lbytes (dd * (size_block p))
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2s_update_multi p dd_prev dd d s =
  repeati dd (blake2s_update_multi_iteration p dd_prev dd d) s


val blake2s_update_last_block:
    p:parameters
  -> ll:size_nat{ll + (size_block p) <= max_size_t}
  -> last_block:lbytes (size_block p)
  -> flag_key:bool
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2s_update_last_block p ll last_block fk s =
  let last_block : lseq (word_t p) 16 = uints_from_bytes_le #p.wt last_block in
  if not fk then
    blake2_compress p s last_block (to_limb p ll) true
  else
    blake2_compress p s last_block (to_limb p (ll + (size_block p))) true


val blake2s_update_last:
    p:parameters
  -> ll:size_nat{ll + (size_block p) <= max_size_t}
  -> len:size_nat{len <= (size_block p)}
  -> last:lbytes len
  -> flag_key:bool
  -> s:hash_state_s p ->
  Tot (hash_state_s p)

let blake2s_update_last p ll len last fk s =
  let last_block = create (size_block p) (u8 0) in
  let last_block = update_sub last_block 0 len last in
  blake2s_update_last_block p ll last_block fk s


val blake2s_update_last_empty: p:parameters -> s:hash_state_s p -> Tot (hash_state_s p)
let blake2s_update_last_empty p st =
  let data = create (size_block p) (u8 0) in
  blake2s_update_last p 0 (size_block p) data false st


val blake2s_finish:
    p:parameters
  -> s:hash_state_s p
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2s_finish p s nn =
  let full = uints_to_bytes_le s in
  sub full 0 nn


val blake2s:
    p:parameters
  -> ll:size_nat{ll + 2 * (size_block p) <= max_size_t} // This could be relaxed
  -> d:lbytes ll
  -> kk:size_nat{kk <= 32}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2s p ll d kk k nn =
  let fk = if kk = 0 then false else true in
  let rem = ll % (size_block p) in
  let nblocks = ll / (size_block p) in
  let blocks = sub d 0 (nblocks * (size_block p)) in
  let last = sub d (nblocks * (size_block p)) rem in
  let s = blake2s_init p kk k nn in
  let s =
    if ll = 0 && kk = 0 then blake2s_update_last_empty p s
    else begin
      let nprev = if kk = 0 then 0 else 1 in
      let s = blake2s_update_multi p nprev nblocks blocks s in
      blake2s_update_last p ll rem last fk s end in
  blake2s_finish p s nn





///
/// Instanciation
///

(* Constants *)
inline_for_extraction
let rTable_list_S = [
  size 16; size 12; size 8; size 7
]

inline_for_extraction
let rTable_list_B = [
  size 32; size 24; size 16; size 63
]

inline_for_extraction let list_iv_S =
  [@inline_let]
  let l =
  [u32 0x6A09E667; u32 0xBB67AE85; u32 0x3C6EF372; u32 0xA54FF53A;
   u32 0x510E527F; u32 0x9B05688C; u32 0x1F83D9AB; u32 0x5BE0CD19] in
  assert_norm(List.Tot.length l <= max_size_t);
  l

inline_for_extraction let list_iv_B =
  List.Tot.map u64
  [0x6A09E667F3BCC908; 0xBB67AE8584CAA73B;
   0x3C6EF372FE94F82B; 0xA54FF53A5F1D36F1;
   0x510E527FADE682D1; 0x9B05688C2B3E6C1F;
   0x1F83D9ABFB41BD6B; 0x5BE0CD19137E2179]
