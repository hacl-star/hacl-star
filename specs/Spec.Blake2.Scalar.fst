module Spec.Blake2.Scalar

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Spec.Blake2


inline_for_extraction
unfold let state_s (a:alg) = lseq (word_t a) 16

let idx = n:nat {n < 16}

(* Functions *)
let g1 (a:alg) (wv:state_s a) (i j:idx) (r:rotval (wt a)) : Tot (state_s a) =
  wv.[i] <- (wv.[i] ^. wv.[j]) >>>. r

let g2 (a:alg) (wv:state_s a) (i j:idx) (x:word_t a) : Tot (state_s a) =
  wv.[i] <- (wv.[i] +. wv.[j] +. x)

let g2z (a:alg) (wv:state_s a) (i j:idx) : Tot (state_s a) =
  wv.[i] <- (wv.[i] +. wv.[j])


val blake2_mixing (al:alg) (wv:state_s al) (a b c d:idx) (x y:word_t al): (state_s al)

let blake2_mixing al wv a b c d x y =
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

let gather_state (al:alg) (m:block_w al) (start:nat{start <= 144}) : state_s al =
  let m0 = m.[v sigmaTable.[start]] in
  let m1 = m.[v sigmaTable.[start+1]] in
  let m2 = m.[v sigmaTable.[start+2]] in
  let m3 = m.[v sigmaTable.[start+3]] in
  let m4 = m.[v sigmaTable.[start+4]] in
  let m5 = m.[v sigmaTable.[start+5]] in
  let m6 = m.[v sigmaTable.[start+6]] in
  let m7 = m.[v sigmaTable.[start+7]] in
  let m8 = m.[v sigmaTable.[start+8]] in
  let m9 = m.[v sigmaTable.[start+9]] in
  let m10 = m.[v sigmaTable.[start+10]] in
  let m11 = m.[v sigmaTable.[start+11]] in
  let m12 = m.[v sigmaTable.[start+12]] in
  let m13 = m.[v sigmaTable.[start+13]] in
  let m14 = m.[v sigmaTable.[start+14]] in
  let m15 = m.[v sigmaTable.[start+15]] in
  let l = [m0;m1;m2;m3;m4;m5;m6;m7;m8;m9;m10;m11;m12;m13;m14;m15] in
  assert_norm (List.Tot.length l == 16);
  createL l

val blake2_round:
    a:alg
  -> m:block_w a
  -> i:size_nat
  -> wv:state_s a
  -> state_s a

let blake2_round alg m i st =
  let start = (i%10) * 16 in
  let m_s = gather_state alg m start in
  let st = blake2_mixing alg st 0 4 8 12 m_s.[0] m_s.[1] in
  let st = blake2_mixing alg st 1 5 9 13 m_s.[2] m_s.[3] in
  let st = blake2_mixing alg st 2 6 10 14 m_s.[4] m_s.[5] in
  let st = blake2_mixing alg st 3 7 11 15 m_s.[6] m_s.[7] in
  let st = blake2_mixing alg st 0 5 10 15 m_s.[8] m_s.[9] in
  let st = blake2_mixing alg st 1 6 11 12 m_s.[10] m_s.[11] in
  let st = blake2_mixing alg st 2 7 8 13 m_s.[12] m_s.[13] in
  let st = blake2_mixing alg st 3 4 9 14 m_s.[14] m_s.[15] in
  st


val blake2_compress0:
    a:alg
  -> m:block_s a
  -> block_w a
let blake2_compress0 a m =
  uints_from_bytes_le m

val blake2_compress1:
    a:alg
  -> s_iv:state_s a
  -> offset:limb_t a
  -> flag:bool ->
  Tot (state_s a)

let blake2_compress1 a s_iv offset flag =
  let wv : state_s a = s_iv in
  let low_offset = limb_to_word a offset in
  let high_offset = limb_to_word a (shift_right #(limb_inttype a) offset (size (bits (wt a)))) in
  let m_12 : word_t a = low_offset in
  let m_13 : word_t a = high_offset in
  let m_14 : word_t a = if flag then (ones (wt a) SEC) else zero a in
  let m_15 : word_t a = zero a in
  let wv = wv.[12] <- wv.[12] ^. m_12 in
  let wv = wv.[13] <- wv.[13] ^. m_13 in
  let wv = wv.[14] <- wv.[14] ^. m_14 in
  let wv = wv.[15] <- wv.[15] ^. m_15 in
  wv


val blake2_compress2:
    a:alg
  -> wv:state_s a
  -> m:block_w a ->
  Tot (state_s a)

let blake2_compress2 a wv m = repeati (rounds a) (blake2_round a m) wv

val blake2_compress3:
    a:alg
  -> wv:state_s a
  -> s_iv:state_s a ->
  Tot (state_s a)

let blake2_compress3 a wv s =
  let s = s.[0] <- (s.[0] ^. wv.[0]) ^. wv.[8] in
  let s = s.[1] <- (s.[1] ^. wv.[1]) ^. wv.[9] in
  let s = s.[2] <- (s.[2] ^. wv.[2]) ^. wv.[10] in
  let s = s.[3] <- (s.[3] ^. wv.[3]) ^. wv.[11] in
  let s = s.[4] <- (s.[4] ^. wv.[4]) ^. wv.[12] in
  let s = s.[5] <- (s.[5] ^. wv.[5]) ^. wv.[13] in
  let s = s.[6] <- (s.[6] ^. wv.[6]) ^. wv.[14] in
  let s = s.[7] <- (s.[7] ^. wv.[7]) ^. wv.[15] in
  s

val blake2_compress:
    a:alg
  -> s_iv:state_s a
  -> m:block_s a
  -> offset:limb_t a
  -> flag:bool ->
  Tot (state_s a)

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
  -> s_iv:state_s a ->
  Tot (state_s a)

let blake2_update_block a flag totlen d s =
  let offset = nat_to_limb a totlen in
  blake2_compress a s d offset flag

val blake2_update1:
    a:alg
  -> prev:nat
  -> m:bytes
  -> i:nat{i < length m / size_block a /\ prev + length m <= max_limb a}
  -> s:state_s a ->
  Tot (state_s a)

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
  -> s:state_s a ->
  Tot (state_s a)

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
  -> s:state_s a ->
  Tot (state_s a)

let split (a:alg) (len:nat)
  : nb_rem:(nat & nat){let (nb,rem) = nb_rem in
		   nb * size_block a + rem == len} =
  let nb = len / size_block a in
  let rem = len % size_block a in
  let nb' = if rem = 0 && nb > 0 then nb - 1 else nb in
  let rem' = if rem = 0 && nb > 0 then size_block a else rem in
  (nb',rem')

let blake2_update_blocks a prev m s =
  let (nb,rem) = split a (length m) in
  let s = repeati nb (blake2_update1 a prev m) s in
  blake2_update_last a prev rem m s


val blake2_init_hash:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (state_s a)

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
  let l = [iv0';iv1;iv2;iv3;iv4;iv5;iv6;iv7;iv0;iv1;iv2;iv3;iv4;iv5;iv6;iv7] in
  assert_norm (List.Tot.length l == 16);
  createL l


val blake2_init:
    a:alg
  -> kk:size_nat{kk <= max_key a}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (state_s a)

let blake2_init a kk k nn =
  let key_block = create (size_block a) (u8 0) in
  let s = blake2_init_hash a kk nn in
  if kk = 0 then s
  else begin
    let key_block = update_sub key_block 0 kk k in
    blake2_update1 a 0 key_block 0 s end


val blake2_finish:
    a:alg
  -> s:state_s a
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let blake2_finish a s nn =
  let full = uints_to_bytes_le (sub s 0 8) in
  sub full 0 nn

val blake2:
    a:alg
  -> d:bytes
  -> kk:size_nat{kk <= max_key a /\ (if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= max_output a} ->
  Tot (lbytes nn)

let compute_prev0 a kk =
  let kn = if kk = 0 then 0 else 1 in
  let prev0 = kn * (size_block a) in
  prev0

#push-options "--z3rlimit 50"
let blake2 a d kk k nn =
  let prev0 = compute_prev0 a kk in
  let s = blake2_init a kk k nn in
  let s = blake2_update_blocks a prev0 d s in
  blake2_finish a s nn
#pop-options

val blake2s:
    d:bytes
  -> kk:size_nat{kk <= 32 /\ (if kk = 0 then length d < pow2 64 else length d + 64 < pow2 64)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 32} ->
  Tot (lbytes nn)

let blake2s d kk k n = blake2 Blake2S d kk k n


val blake2b:
    d:bytes
  -> kk:size_nat{kk <= 64 /\ (if kk = 0 then length d < pow2 128 else length d + 128 < pow2 128)}
  -> k:lbytes kk
  -> nn:size_nat{1 <= nn /\ nn <= 64} ->
  Tot (lbytes nn)

let blake2b d kk k n = blake2 Blake2B d kk k n
