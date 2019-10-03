module Spec.Blake2

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

#set-options "--z3rlimit 25"

type alg =
  | Blake2S
  | Blake2B

inline_for_extraction
let wt (a:alg) : t:inttype{unsigned t} =
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
inline_for_extraction let size_ivTable : size_nat = 8
inline_for_extraction let size_sigmaTable : size_nat = 160

inline_for_extraction let max_key (a:alg) =
  match a with
  | Blake2S -> 32
  | Blake2B -> 64
inline_for_extraction let max_output (a:alg) =
  match a with
  | Blake2S -> 32
  | Blake2B -> 64


(* Definition of base types *)
inline_for_extraction
unfold let limb_inttype (a:alg) =
  match (wt a) with
  | U32 -> U64
  | U64 -> U128

unfold type word_t (a:alg) = uint_t (wt a) SEC
type pub_word_t (a:alg) = uint_t (wt a) PUB
type limb_t (a:alg) : Type0 = uint_t (limb_inttype a) SEC

inline_for_extraction
let max_limb (a:alg) = maxint (limb_inttype a)

inline_for_extraction
let nat_to_word (a:alg) (x:size_nat) : word_t a =
  match (wt a) with
  | U32 -> u32 x
  | U64 -> u64 x

inline_for_extraction
let nat_to_limb (a:alg) (x:nat{x <= max_limb a}) : xl:limb_t a{uint_v xl == x} =
  match (wt a) with
  | U32 -> u64 x
  | U64 -> admit(); u128 x

inline_for_extraction
let word_to_limb (a:alg) (x:word_t a{uint_v x <= max_limb a}) : xl:limb_t a{uint_v xl == uint_v x} =
  match (wt a) with
  | U32 -> to_u64 x
  | U64 -> to_u128 x

inline_for_extraction
let limb_to_word (a:alg) (x:limb_t a) : word_t a =
  match (wt a) with
  | U32 -> to_u32 x
  | U64 -> to_u64 x

unfold let rtable_t (a:alg) = lseq (rotval (wt a)) 4

[@"opaque_to_smt"]
inline_for_extraction
let rTable_list_S : l:List.Tot.llist (rotval U32) 4 =
  [
    size 16; size 12; size 8; size 7
  ]

[@"opaque_to_smt"]
inline_for_extraction
let rTable_list_B: l:List.Tot.llist (rotval U64) 4 =
  [
    size 32; size 24; size 16; size 63
  ]

inline_for_extraction
let rTable (a:alg) : rtable_t a =
  match a with
  | Blake2S -> (of_list rTable_list_S)
  | Blake2B -> (of_list rTable_list_B)

[@"opaque_to_smt"]
inline_for_extraction
let list_iv_S: l:List.Tot.llist (uint_t U32 PUB) 8 =
  [@inline_let]
  let l = [
    0x6A09E667ul; 0xBB67AE85ul; 0x3C6EF372ul; 0xA54FF53Aul;
    0x510E527Ful; 0x9B05688Cul; 0x1F83D9ABul; 0x5BE0CD19ul] in
  assert_norm(List.Tot.length l == 8);
  l

[@"opaque_to_smt"]
inline_for_extraction
let list_iv_B: List.Tot.llist (uint_t U64 PUB) 8 =
  [@inline_let]
  let l = [
    0x6A09E667F3BCC908uL; 0xBB67AE8584CAA73BuL;
    0x3C6EF372FE94F82BuL; 0xA54FF53A5F1D36F1uL;
    0x510E527FADE682D1uL; 0x9B05688C2B3E6C1FuL;
    0x1F83D9ABFB41BD6BuL; 0x5BE0CD19137E2179uL] in
  assert_norm(List.Tot.length l == 8);
  l

[@"opaque_to_smt"]
inline_for_extraction
let list_iv (a:alg): List.Tot.llist (pub_word_t a) 8 =
  match a with
  | Blake2S -> list_iv_S
  | Blake2B -> list_iv_B

inline_for_extraction
let ivTable (a:alg) : lseq (pub_word_t a) 8 =
  match a with
  | Blake2S -> of_list list_iv_S
  | Blake2B -> of_list list_iv_B


type sigma_elt_t = n:size_t{size_v n < 16}
type list_sigma_t = l:list sigma_elt_t{List.Tot.length l == 160}

[@"opaque_to_smt"]
inline_for_extraction
let list_sigma: list_sigma_t =
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
  assert_norm(List.Tot.length l == 160);
  l

inline_for_extraction
let sigmaTable:lseq sigma_elt_t size_sigmaTable =
  assert_norm (List.Tot.length list_sigma == size_sigmaTable);
  of_list list_sigma


(* Algorithms types *)
type vector_ws (a:alg) = lseq (word_t a) size_block_w
type block_ws (a:alg) = lseq (word_t a) size_block_w
type block_s (a:alg) = lseq uint8 (size_block a)
type hash_ws (a:alg) = lseq (word_t a) size_hash_w
type idx_t = n:size_nat{n < 16}


(* Functions *)
let g1 (a:alg) (wv:vector_ws a) (i:idx_t) (j:idx_t) (r:rotval (wt a)) : Tot (vector_ws a) =
  wv.[i] <- (wv.[i] ^. wv.[j]) >>>. r

let g2 (a:alg) (wv:vector_ws a) (i:idx_t) (j:idx_t) (x:word_t a) : Tot (vector_ws a) =
  wv.[i] <- (wv.[i] +. wv.[j] +. x)


val blake2_mixing:
    a:alg
  -> ws:vector_ws a
  -> idx_t
  -> idx_t
  -> idx_t
  -> idx_t
  -> word_t a
  -> word_t a ->
  Tot (vector_ws a)

let blake2_mixing al wv a b c d x y =
  let rt = rTable al in
  let wv = g2 al wv a b x in
  let wv = g1 al wv d a rt.[0] in
  let wv = g2 al wv c d (nat_to_word al 0) in
  let wv = g1 al wv b c rt.[1] in
  let wv = g2 al wv a b y in
  let wv = g1 al wv d a rt.[2] in
  let wv = g2 al wv c d (nat_to_word al 0) in
  let wv = g1 al wv b c rt.[3] in
  wv


val blake2_round1:
    a:alg
  -> wv:vector_ws a
  -> m:block_ws a
  -> i:size_nat ->
  Tot (vector_ws a)

let blake2_round1 a wv m i =
  let start = ((i % 10) * 16) in
  let s0 = size_v sigmaTable.[start + 0] in
  let s1 = size_v sigmaTable.[start + 1] in
  let s2 = size_v sigmaTable.[start + 2] in
  let s3 = size_v sigmaTable.[start + 3] in
  let s4 = size_v sigmaTable.[start + 4] in
  let s5 = size_v sigmaTable.[start + 5] in
  let s6 = size_v sigmaTable.[start + 6] in
  let s7 = size_v sigmaTable.[start + 7] in
  let wv = blake2_mixing a wv 0 4  8 12 (m.[s0]) (m.[s1]) in
  let wv = blake2_mixing a wv 1 5  9 13 (m.[s2]) (m.[s3]) in
  let wv = blake2_mixing a wv 2 6 10 14 (m.[s4]) (m.[s5]) in
  let wv = blake2_mixing a wv 3 7 11 15 (m.[s6]) (m.[s7]) in
  wv


val blake2_round2:
    a:alg
  -> wv:vector_ws a
  -> m:block_ws a
  -> i:size_nat ->
  Tot (vector_ws a)

let blake2_round2 a wv m i =
  let start = ((i % 10) * 16) in
  let s8 = size_v sigmaTable.[start + 8] in
  let s9 = size_v sigmaTable.[start + 9] in
  let s10 = size_v sigmaTable.[start + 10] in
  let s11 = size_v sigmaTable.[start + 11] in
  let s12 = size_v sigmaTable.[start + 12] in
  let s13 = size_v sigmaTable.[start + 13] in
  let s14 = size_v sigmaTable.[start + 14] in
  let s15 = size_v sigmaTable.[start + 15] in
  let wv = blake2_mixing a wv 0 5 10 15 (m.[s8]) (m.[s9]) in
  let wv = blake2_mixing a wv 1 6 11 12 (m.[s10]) (m.[s11]) in
  let wv = blake2_mixing a wv 2 7  8 13 (m.[s12]) (m.[s13]) in
  let wv = blake2_mixing a wv 3 4  9 14 (m.[s14]) (m.[s15]) in
  wv


val blake2_round:
    a:alg
  -> m:block_ws a
  -> i:size_nat
  -> wv:vector_ws a ->
  Tot (vector_ws a)

let blake2_round a m i wv =
  let wv = blake2_round1 a wv m i in
  let wv = blake2_round2 a wv m i in
  wv


val blake2_compress1:
    a:alg
  -> wv:vector_ws a
  -> s:hash_ws a
  -> m:block_ws a
  -> offset:limb_t a
  -> flag:bool ->
  Tot (vector_ws a)

let blake2_compress1 a wv s m offset flag =
  let iv = map secret (ivTable a) in
  let wv = update_sub wv 0 8 s in
  let wv = update_sub wv 8 8 iv in
  let low_offset = limb_to_word a offset in
  let high_offset = limb_to_word a (shift_right #(limb_inttype a) offset (size (bits (wt a)))) in
  let wv_12 = wv.[12] ^. low_offset in
  let wv_13 = wv.[13] ^. high_offset in
  let wv_14 = wv.[14] ^. (ones (wt a) SEC) in
  let wv = wv.[12] <- wv_12 in
  let wv = wv.[13] <- wv_13 in
  let wv = if flag then wv.[14] <- wv_14 else wv in
  wv


val blake2_compress2:
    a:alg
  -> wv:vector_ws a
  -> m:block_ws a ->
  Tot (vector_ws a)

let blake2_compress2 a wv m = repeati (rounds a) (blake2_round a m) wv


val blake2_compress3_inner:
    a:alg
  -> ws:vector_ws a
  -> i:size_nat{i < 8}
  -> s:hash_ws a ->
  Tot (hash_ws a)

let blake2_compress3_inner a wv i s =
  let i_plus_8 = i + 8 in
  let si_xor_wvi = logxor #(wt a) s.[i] wv.[i] in
  let si = logxor #(wt a) si_xor_wvi wv.[i_plus_8] in
  s.[i] <- si


val blake2_compress3:
    a:alg
  -> ws:vector_ws a
  -> s:hash_ws a ->
  Tot (hash_ws a)

let blake2_compress3 a wv s = repeati 8 (blake2_compress3_inner a wv) s


val blake2_compress:
    a:alg
  -> s:hash_ws a
  -> m:block_ws a
  -> offset:limb_t a
  -> flag:bool ->
  Tot (hash_ws a)

let blake2_compress a s m offset flag =
  let wv = create 16 (nat_to_word a 0) in
  let wv = blake2_compress1 a wv s m offset flag in
  let wv = blake2_compress2 a wv m in
  let s = blake2_compress3 a wv s in
  s


val blake2_update_block:
    a:alg
  -> flag:bool
  -> totlen:nat{totlen <= max_limb a}
  -> d:block_s a
  -> s:hash_ws a ->
  Tot (hash_ws a)

let blake2_update_block a flag totlen d s =
  let to_compress : lseq (word_t a) 16 = uints_from_bytes_le #(wt a) #SEC d in
  let offset = nat_to_limb a totlen in
  blake2_compress a s to_compress offset flag


val blake2_update_block_multi:
    a:alg
  -> prev:nat
  -> n:nat
  -> blocks:bytes{n * size_block a == length blocks /\ prev + n * size_block a <= max_limb a}
  -> s:hash_ws a ->
  Tot (hash_ws a)

let blake2_update_block_multi a prev n blocks s =
  repeati n (fun i si ->
    let block = Seq.slice blocks (i * size_block a) ((i + 1) * (size_block a)) in
    blake2_update_block a false (prev + (i + 1) * size_block a) block si
  ) s


val blake2_init_hash:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (hash_ws a)

let blake2_init_hash a kk nn =
  let s = map secret (ivTable a) in
  let s0 = s.[0] in
  let s0' = s0 ^. (nat_to_word a 0x01010000) ^. ((nat_to_word a kk) <<. (size 8)) ^. (nat_to_word a nn) in
  s.[0] <- s0'


val blake2_init:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (hash_ws a)

let blake2_init a kk k nn =
  let key_block = create (size_block a) (u8 0) in
  let s = blake2_init_hash a kk nn in
  if kk = 0 then s
  else begin
    let key_block = update_sub key_block 0 kk k in
    blake2_update_block a false (size_block a) key_block s end


val blake2_update_last:
    a:alg
  -> prev:nat
  -> len:size_nat{len <= size_block a /\ prev + len <= max_limb a}
  -> last:lbytes len
  -> s:hash_ws a ->
  Tot (hash_ws a)

let blake2_update_last a prev len last s =
  let last_block = create (size_block a) (u8 0) in
  let last_block = update_sub last_block 0 len last in
  blake2_update_block a true (prev + len) last_block s


val blake2_finish:
    a:alg
  -> s:hash_ws a
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2_finish a s nn =
  let full = uints_to_bytes_le s in
  sub full 0 nn


val blake2:
    a:alg
  -> d:bytes
  -> kk:size_nat{kk <= max_key a /\ (if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2 a d kk k nn =
  let ll = Seq.length d in
  let n = ll / size_block a in
  let rem = ll % size_block a in
  let n,rem = if n <> 0 && rem = 0 then n - 1, size_block a else n, rem in
  let blocks = Seq.slice #uint8 d 0 (n * size_block a) in
  let last = Seq.slice #uint8 d (n * size_block a) ll in
  let kn = if kk = 0 then 0 else 1 in
  let s: hash_ws a = blake2_init a kk k nn in
  let s: hash_ws a = blake2_update_block_multi a (kn * size_block a) n blocks s in
  let s: hash_ws a = blake2_update_last a ((kn + n) * size_block a) rem last s in
  blake2_finish a s nn


val blake2s:
    d:bytes
  -> kk:size_nat{kk <= 32 /\ (if kk = 0 then length d < pow2 64 else length d + 64 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2s d kk k n = blake2 Blake2S d kk k n


val blake2b:
    d:bytes
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then length d < pow2 128 else length d + 128  < pow2 128)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  Tot (lbytes nn)

let blake2b d kk k n = blake2 Blake2B d kk k n


(* let spec_update_block *)
(*     (a:alg) *)
(*     (flag:bool) *)
(*     (init:nat) *)
(*     (i:nat{init + (i * size_block a) <= max_limb a}) = *)
(*     blake2_update_block a flag (init + (i * size_block a)) *)

(* let spec_update_last *)
(*     (a:alg) *)
(*     (len:nat{len <= max_limb a}) *)
(*     (i:nat) = *)
(*     blake2_update_last a len *)

(* val blake2_update: *)
(*     a:alg *)
(*   -> s:hash_ws a *)
(*   -> d:bytes *)
(*   -> kk:size_nat{kk <= max_key a /\ (if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a)} -> *)
(*   Tot (hash_ws a) *)

(* // BB. This naming is just bad. Change it ! *)
(* let blake2_update a s d kk = *)
(*   let ll = length d in *)
(*   let klen = if kk = 0 then 0 else 1 in *)
(*   let flag = length d % size_block a = 0 in *)
(*   repeati_blocks (size_block a) d *)
(*     (spec_update_block a flag ((klen + 1) * size_block a)) *)
(*     (spec_update_last a (klen * (size_block a) + ll)) *)
(*     s *)
