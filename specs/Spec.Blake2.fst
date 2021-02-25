module Spec.Blake2

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
module UpdateMulti = Lib.UpdateMulti

#set-options "--z3rlimit 50"

type alg =
  | Blake2S
  | Blake2B

let alg_inversion_lemma (a:alg) : Lemma (a == Blake2S \/ a == Blake2B) = ()

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

inline_for_extraction
unfold type word_t (a:alg) = uint_t (wt a) SEC

inline_for_extraction
let zero (a:alg) : word_t a=
  match a with
  | Blake2S -> u32 0
  | Blake2B -> u64 0

inline_for_extraction
unfold let row (a:alg) = lseq (word_t a) 4

inline_for_extraction
let zero_row (a:alg) : row a = create 4 (zero a)

inline_for_extraction
let load_row (#a:alg) (s:lseq (word_t a) 4) : row a =
  createL [s.[0]; s.[1]; s.[2]; s.[3]]

inline_for_extraction
let create_row (#a:alg) x0 x1 x2 x3 : row a =
  createL [x0;x1;x2;x3]

inline_for_extraction
unfold let state (a:alg) = lseq (row a) 4

inline_for_extraction
type pub_word_t (a:alg) = uint_t (wt a) PUB

inline_for_extraction
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
  | U64 -> let h = u64 (x / pow2 64) in
	  let l = u64 (x % pow2 64) in
	  (to_u128 h <<. 64ul) +! to_u128 l

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
let rTable_list_S : List.Tot.llist (rotval U32) 4 =
  [
    size 16; size 12; size 8; size 7
  ]

[@"opaque_to_smt"]
inline_for_extraction
let rTable_list_B: List.Tot.llist (rotval U64) 4 =
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
let list_iv_S: List.Tot.llist (uint_t U32 PUB) 8 =
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

let list_sigma: list_sigma_t =
  [@inline_let]
  let l : list sigma_elt_t = [
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
    size 15; size 11; size  9; size 14; size  3; size 12; size 13; size  0
    ] in
  assert_norm(List.Tot.length l == 160);
  l


inline_for_extraction
let sigmaTable:lseq sigma_elt_t size_sigmaTable =
  assert_norm (List.Tot.length list_sigma == size_sigmaTable);
  of_list list_sigma


(* Algorithms types *)
type block_s (a:alg) = lseq uint8 (size_block a)
type block_w (a:alg) = lseq (word_t a) 16
type idx_t = n:size_nat{n < 16}

let row_idx = n:nat {n < 4}

inline_for_extraction
let ( ^| ) (#a:alg) (r1:row a) (r2:row a) : row a =
  map2 ( ^. ) r1 r2

inline_for_extraction
let ( +| ) (#a:alg) (r1:row a) (r2:row a) : row a =
  map2 ( +. ) r1 r2

inline_for_extraction
let ( >>>| ) (#a:alg) (r1:row a) (r:rotval (wt a)) : row a =
  map #(word_t a) (rotate_right_i r) r1

inline_for_extraction
let rotr (#a:alg) (r1:row a) (r:row_idx) : row a =
  createi 4 (fun i -> r1.[(i+r)%4])


(* Functions *)
let g1 (a:alg) (wv:state a) (i:row_idx) (j:row_idx) (r:rotval (wt a)) : Tot (state a) =
  wv.[i] <- (wv.[i] ^| wv.[j]) >>>| r

let g2 (a:alg) (wv:state a) (i:row_idx) (j:row_idx) (x:row a) : Tot (state a) =
  wv.[i] <- (wv.[i] +| wv.[j] +| x)

let g2z (a:alg) (wv:state a) (i:row_idx) (j:row_idx) : Tot (state a) =
  wv.[i] <- (wv.[i] +| wv.[j])


val blake2_mixing:
    a:alg
  -> ws:state a
  -> row a
  -> row a ->
  Tot (state a)

let blake2_mixing al wv x y =
  let a = 0 in
  let b = 1 in
  let c = 2 in
  let d = 3 in
  let rt = rTable al in
  let wv = g2 al wv a b x in
  let wv = g1 al wv d a rt.[0] in
  let wv = g2z al wv c d in
  let wv = g1 al wv b c rt.[1] in
  let wv = g2 al wv a b y in
  let wv = g1 al wv d a rt.[2] in
  let wv = g2z al wv c d in
  let wv = g1 al wv b c rt.[3] in
  wv

let diag (#a:alg) (wv:state a) : state a =
  let wv = wv.[1] <- rotr wv.[1] 1 in
  let wv = wv.[2] <- rotr wv.[2] 2 in
  let wv = wv.[3] <- rotr wv.[3] 3 in
  wv

let undiag (#a:alg) (wv:state a) : state a =
  let wv = wv.[1] <- rotr wv.[1] 3 in
  let wv = wv.[2] <- rotr wv.[2] 2 in
  let wv = wv.[3] <- rotr wv.[3] 1 in
  wv

inline_for_extraction
let gather_row (#a:alg) (m:block_w a) (i0 i1 i2 i3:sigma_elt_t) : row a =
  create_row m.[v i0] m.[v i1] m.[v i2] m.[v i3]
(*  let nb = size_word a in
  let u0 = uint_from_bytes_le #(wt a) #SEC (sub m (v i0*nb) nb) in
  let u1 = uint_from_bytes_le #(wt a) #SEC (sub m (v i1*nb) nb) in
  let u2 = uint_from_bytes_le #(wt a) #SEC (sub m (v i2*nb) nb) in
  let u3 = uint_from_bytes_le #(wt a) #SEC (sub m (v i3*nb) nb) in
  create_row u0 u1 u2 u3
*)

val gather_state: a:alg -> m:block_w a -> start:nat{start <= 144} -> state a
let gather_state a m start =
  let x = gather_row m sigmaTable.[start] sigmaTable.[start+2] sigmaTable.[start+4] sigmaTable.[start+6]  in
  let y = gather_row m sigmaTable.[start+1] sigmaTable.[start+3] sigmaTable.[start+5] sigmaTable.[start+7]  in
  let z = gather_row m sigmaTable.[start+8] sigmaTable.[start+10] sigmaTable.[start+12] sigmaTable.[start+14]  in
  let w = gather_row m sigmaTable.[start+9] sigmaTable.[start+11] sigmaTable.[start+13] sigmaTable.[start+15]  in
  let l = [x;y;z;w] in
  assert_norm (List.Tot.length l == 4);
  createL l

val blake2_round:
    a:alg
  -> m:block_w a
  -> i:size_nat
  -> wv:state a
  -> state a

let blake2_round a m i wv =
  let start = (i%10) * 16 in
  let m_s = gather_state a m start in
  let wv = blake2_mixing a wv m_s.[0] m_s.[1] in
  let wv = diag wv in
  let wv = blake2_mixing a wv m_s.[2] m_s.[3] in
  undiag wv

val blake2_compress0:
    a:alg
  -> m:block_s a
  -> block_w a
let blake2_compress0 a m =
  uints_from_bytes_le m

val blake2_compress1:
    a:alg
  -> s_iv:state a
  -> offset:limb_t a
  -> flag:bool ->
  Tot (state a)

let blake2_compress1 a s_iv offset flag =
  let wv : state a = s_iv in
  let low_offset = limb_to_word a offset in
  let high_offset = limb_to_word a (shift_right #(limb_inttype a) offset (size (bits (wt a)))) in
  let m_12 = low_offset in
  let m_13 = high_offset in
  let m_14 = if flag then (ones (wt a) SEC) else zero a in
  let m_15 = zero a in
  let mask = create_row m_12 m_13 m_14 m_15 in
  let wv = wv.[3] <- wv.[3] ^| mask in
  wv


val blake2_compress2:
    a:alg
  -> wv:state a
  -> m:block_w a ->
  Tot (state a)

let blake2_compress2 a wv m = repeati (rounds a) (blake2_round a m) wv

val blake2_compress3:
    a:alg
  -> wv:state a
  -> s_iv:state a ->
  Tot (state a)

let blake2_compress3 a wv s =
  let s = s.[0] <- (s.[0] ^| wv.[0]) ^| wv.[2] in
  let s = s.[1] <- (s.[1] ^| wv.[1]) ^| wv.[3] in
  s

val blake2_compress:
    a:alg
  -> s_iv:state a
  -> m:block_s a
  -> offset:limb_t a
  -> flag:bool ->
  Tot (state a)

let blake2_compress a s_iv m offset flag =
  let m_w = blake2_compress0 a m in
  let wv = blake2_compress1 a s_iv offset flag in
  let wv = blake2_compress2 a wv m_w in
  let s_iv = blake2_compress3 a wv s_iv in
  s_iv


val blake2_update_block:
    a:alg
  -> flag:bool
  -> totlen:nat{totlen <= max_limb a}
  -> d:block_s a
  -> s_iv:state a ->
  Tot (state a)

let blake2_update_block a flag totlen d s =
  let offset = nat_to_limb a totlen in
  blake2_compress a s d offset flag

val blake2_update1:
    a:alg
  -> prev:nat
  -> m:bytes
  -> i:nat{i < length m / size_block a /\ prev + length m <= max_limb a}
  -> s:state a ->
  Tot (state a)

let get_blocki (a:alg) (m:bytes) (i:nat{i < length m / size_block a}) : block_s a =
  Seq.slice m (i * size_block a) ((i+1) * size_block a)

let blake2_update1 a prev m i s =
  let totlen = prev + (i+1) * size_block a in
  let d = get_blocki a m i in
  blake2_update_block a false totlen d s

val blake2_update_last:
    a:alg
  -> prev:nat
  -> rem:nat
  -> m:bytes{prev + length m <= max_limb a /\ rem <= length m /\ rem <= size_block a}
  -> s:state a ->
  Tot (state a)

let get_last_padded_block (a:alg) (m:bytes)
    (rem:nat{rem <= length m /\ rem <= size_block a}) : block_s a =
  let last = Seq.slice m (length m - rem) (length m) in
  let last_block = create (size_block a) (u8 0) in
  let last_block = update_sub last_block 0 rem last in
  last_block

let blake2_update_last a prev rem m s =
  let inlen = length m in
  let totlen = prev + inlen in
  let last_block = get_last_padded_block a m rem in
  blake2_update_block a true totlen last_block s

val blake2_update_blocks:
    a:alg
  -> prev:nat
  -> m:bytes{prev + length m <= max_limb a}
  -> s:state a ->
  Tot (state a)

let split (a:alg) (len:nat)
  : nb_rem:(nat & nat){let (nb,rem) = nb_rem in
		   nb * size_block a + rem == len} =
  UpdateMulti.split_at_last_lazy_nb_rem (size_block a) len

let blake2_update_blocks a prev m s =
  let (nb,rem) = split a (length m) in
  let s = repeati nb (blake2_update1 a prev m) s in
  blake2_update_last a prev rem m s


val blake2_init_hash:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (state a)

let blake2_init_hash a kk nn =
  let iv0 = secret (ivTable a).[0] in
  let iv1 = secret (ivTable a).[1] in
  let iv2 = secret (ivTable a).[2] in
  let iv3 = secret (ivTable a).[3] in
  let iv4 = secret (ivTable a).[4] in
  let iv5 = secret (ivTable a).[5] in
  let iv6 = secret (ivTable a).[6] in
  let iv7 = secret (ivTable a).[7] in
  let r0 = create_row #a iv0 iv1 iv2 iv3 in
  let r1 = create_row #a iv4 iv5 iv6 iv7 in
  let s0' = (nat_to_word a 0x01010000) ^. ((nat_to_word a kk) <<. (size 8)) ^. (nat_to_word a nn) in
  let iv0' = iv0 ^. s0' in
  let r0' = create_row #a iv0' iv1 iv2 iv3 in
  let s_iv = createL [r0';r1;r0;r1] in
  s_iv

val blake2_init:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (state a)

let blake2_init a kk k nn =
  let key_block = create (size_block a) (u8 0) in
  let s = blake2_init_hash a kk nn in
  if kk = 0 then s
  else begin
    let key_block = update_sub key_block 0 kk k in
    blake2_update1 a 0 key_block 0 s end

val blake2_finish:
    a:alg
  -> s:state a
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2_finish a s nn =
  let full = (uints_to_bytes_le s.[0] @| uints_to_bytes_le s.[1]) in
  sub full 0 nn

val blake2:
    a:alg
  -> d:bytes
  -> kk:size_nat{kk <= max_key a /\ (if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

(* TODO: SH: this definition is awkward to use because of the multiplication.
 * Wouldn't it be possible to simply write the following?
 * [if kk = 0 then 0 else size_block a]
 * It is actually shorter and clearer. *)
let compute_prev0 a kk =
  let kn = if kk = 0 then 0 else 1 in
  let prev0 = kn * (size_block a) in
  prev0

let blake2 a d kk k nn =
  let prev0 = compute_prev0 a kk in
  let s = blake2_init a kk k nn in
  let s = blake2_update_blocks a prev0 d s in
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
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then length d < pow2 128 else length d + 128 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  Tot (lbytes nn)

let blake2b d kk k n = blake2 Blake2B d kk k n
