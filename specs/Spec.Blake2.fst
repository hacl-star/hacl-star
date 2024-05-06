module Spec.Blake2

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
module UpdateMulti = Lib.UpdateMulti

include Spec.Blake2.Definitions

#set-options "--z3rlimit 50"

/// Serialize blake2s parameters to be xor'ed with the state during initialization
/// As the state is represented using uint32, we need to serialize to uint32 instead
/// of the more standard bytes representation
let serialize_blake2s_params (p: blake2_params Blake2S) : lseq uint32 8 =
  let s0 = (u32 (v #U8 #PUB p.digest_length)) ^.
           (u32 (v #U8 #PUB p.key_length) <<. (size 8)) ^.
           (u32 (v p.fanout) <<. (size 16)) ^.
           (u32 (v p.depth) <<. (size 24)) in
  let s1 = p.leaf_length in
  (* Take the first four bytes *)
  let s2 = (to_u32 p.node_offset) in
  (* Take the last four bytes of node_offset *)
  let s3 = (to_u32 (p.node_offset >>. (size 32))) ^.
           (u32 (v p.node_depth) <<. (size 16)) ^.
           (u32 (v p.inner_length) <<. (size 24)) in
  let salt_u32: lseq uint32 2 = uints_from_bytes_le p.salt in
  let s4 = salt_u32.[0] in
  let s5 = salt_u32.[1] in
  let personal_u32: lseq uint32 2 = uints_from_bytes_le p.personal in
  let s6 = personal_u32.[0] in
  let s7 = personal_u32.[1] in
  [@inline_let]
  let l = [s0; s1; s2; s3; s4; s5; s6; s7] in
  assert_norm (List.Tot.length l == 8);
  createL l

/// Serialize blake2b parameters to be xor'ed with the state during initialization
/// As the state is represented using uint64, we need to serialize to uint64 instead
/// of the more standard bytes representation
let serialize_blake2b_params (p: blake2_params Blake2B) : lseq uint64 8 =
  let s0 = (u64 (v #U8 #PUB p.digest_length)) ^.
           (u64 (v #U8 #PUB p.key_length) <<. (size 8)) ^.
           (u64 (v p.fanout) <<. (size 16)) ^.
           (u64 (v p.depth) <<. (size 24)) ^.
           (u64 (v p.leaf_length) <<. (size 32)) in
  let s1 = p.node_offset in
  // The serialization corresponding to s2 contains node_depth and inner_length,
  // followed by the 14 reserved bytes which always seem to be zeros, and can hence
  // be ignored when building the corresponding uint64 using xor's
  let s2 = (u64 (v p.node_depth)) ^.
           (u64 (v p.inner_length) <<. (size 8)) in
  // s3 corresponds to the remaining of the reserved bytes
  let s3 = u64 0 in
  let salt_u64: lseq uint64 2 = uints_from_bytes_le p.salt in
  let s4 = salt_u64.[0] in
  let s5 = salt_u64.[1] in
  let personal_u64: lseq uint64 2 = uints_from_bytes_le p.personal in
  let s6 = personal_u64.[0] in
  let s7 = personal_u64.[1] in
  [@inline_let]
  let l = [s0; s1; s2; s3; s4; s5; s6; s7] in
  assert_norm (List.Tot.length l == 8);
  createL l

inline_for_extraction
let serialize_blake2_params (#a: alg) (p: blake2_params a): lseq (word_t a) 8 =
  match a with
  | Blake2S -> serialize_blake2s_params p
  | Blake2B -> serialize_blake2b_params p


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
  -> blake2_params a ->
  Tot (state a)

let blake2_init_hash a p =
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
  let s = serialize_blake2_params p in
  let iv0' = iv0 ^. s.[0] in
  let iv1' = iv1 ^. s.[1] in
  let iv2' = iv2 ^. s.[2] in
  let iv3' = iv3 ^. s.[3] in
  let iv4' = iv4 ^. s.[4] in
  let iv5' = iv5 ^. s.[5] in
  let iv6' = iv6 ^. s.[6] in
  let iv7' = iv7 ^. s.[7] in
  let r0' = create_row #a iv0' iv1' iv2' iv3' in
  let r1' = create_row #a iv4' iv5' iv6' iv7' in
  let s_iv = createL [r0';r1';r0;r1] in
  s_iv

val blake2_key_block:
    a:alg
  -> kk:size_nat{0 < kk /\ kk <= max_key a}
  -> k:lbytes kk
  -> block_s a
let blake2_key_block a kk k =
  let key_block = create (size_block a) (u8 0) in
  let key_block = update_sub key_block 0 kk k in
  key_block

/// This function must be called only if the key is non empty (see the precondition)
val blake2_update_key:
    a:alg
  -> kk:size_nat{0 < kk /\ kk <= max_key a}
  -> k:lbytes kk
  -> ll:nat
  -> s:state a ->
  Tot (state a)
let blake2_update_key a kk k ll s =
  let key_block = blake2_key_block a kk k in
  if ll = 0 then
      blake2_update_block a true (size_block a) key_block s
  else
      blake2_update_block a false (size_block a) key_block s

val blake2_update:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> k:lbytes kk
  -> d:bytes{if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a}
  -> s:state a ->
  Tot (state a)
let blake2_update a kk k d s =
  let ll = length d in
  if kk > 0 then
     let s = blake2_update_key a kk k ll s in
     if ll = 0 then s // Skip update_last if ll = 0 (but kk > 0)
     else blake2_update_blocks a (size_block a) d s
  else blake2_update_blocks a 0 d s

val blake2_finish:
    a:alg
  -> s:state a
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2_finish a s nn =
  let full = (uints_to_bytes_le s.[0] @| uints_to_bytes_le s.[1]) in
  sub full 0 nn

// Full generality, with parameters
val blake2:
    a:alg
  -> d:bytes
  -> p:blake2_params a {
      let kk = p.key_length in
      if kk = 0uy then length d <= max_limb a else length d + (size_block a) <= max_limb a
  }
  -> k:lbytes (UInt8.v p.key_length) ->
  Tot (lbytes (UInt8.v p.digest_length))

let blake2 a d p k =
  let kk = UInt8.v p.key_length in
  let nn = UInt8.v p.digest_length in
  let s = blake2_init_hash a p in
  let s = blake2_update a kk k d s in
  blake2_finish a s nn

// Simplified API, no parameters
val blake2s:
    d:bytes
  -> kk:size_nat{kk <= 32 /\ (if kk = 0 then length d < pow2 64 else length d + 64 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2s d kk k n = blake2 Blake2S d { blake2_default_params Blake2S with key_length = UInt8.uint_to_t kk; digest_length = UInt8.uint_to_t n } k

val blake2b:
    d:bytes
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then length d < pow2 128 else length d + 128 < pow2 128)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  Tot (lbytes nn)

let blake2b d kk k n = blake2 Blake2B d { blake2_default_params Blake2B with key_length = UInt8.uint_to_t kk; digest_length = UInt8.uint_to_t n } k

