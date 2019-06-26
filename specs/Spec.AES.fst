module Spec.AES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Spec.GaloisField


/// Constants and Types

(* GF(8) Field  *)
let irred = u8 0x1b
let gf8 = gf U8 irred
let elem = felem gf8
let to_elem = to_felem #gf8
let zero = to_elem 0
let two = to_elem 2
let three = to_elem 3

(* These operations are normalized here to avoid a huge blowup in generate code size *)
let ( <<<. ) x y = normalize_term (rotate_left #U8 #SEC x y)
let ( ^. ) x y = normalize_term (logxor #U8 #SEC x y)

(* Specification of the Rijndael S-Box : *)
type word = lseq elem 4
type block = lseq elem 16

type variant = | AES128 | AES256

let num_rounds (v:variant) =
  match v with
  | AES128 -> 10
  | AES256 -> 14

let key_size (v:variant) =
  match v with
  | AES128 -> 16
  | AES256 -> 32

let aes_key (v:variant) = lbytes (key_size v)
let aes_xkey (v:variant) = lseq elem ((num_rounds v+1) * 16)
let aes_ikey (v:variant) = lseq elem ((num_rounds v-1) * 16)


let sub_byte (input:elem) =
  let s = finv input in
  s ^.
  (s <<<. size 1) ^.
  (s <<<. size 2) ^.
  (s <<<. size 3) ^.
  (s <<<. size 4) ^.
  (to_elem 99)

let inv_sub_byte (input:elem) =
  let s = input in
  let s:elem =
    (s <<<. size 1) ^.
    (s <<<. size 3) ^.
    (s <<<. size 6) ^.
    (u8 5)
  in
  finv s

let subBytes (state:block) : Tot block =
  map sub_byte state

let inv_subBytes (state:block) : Tot block =
  map inv_sub_byte state

let shiftRow (i:size_nat{i < 4}) (shift:size_nat{i < 4}) (state:block) : Tot block =
  let tmp0 = state.[i + (4 * (shift % 4))] in
  let tmp1 = state.[i + (4 * ((shift + 1) % 4))] in
  let tmp2 = state.[i + (4 * ((shift + 2) % 4))] in
  let tmp3 = state.[i + (4 * ((shift + 3) % 4))] in
  let state = state.[i] <- tmp0 in
  let state = state.[i+4] <- tmp1 in
  let state = state.[i+8] <- tmp2 in
  let state = state.[i+12] <- tmp3 in
  state

let shiftRows (state: block) : Tot block =
  let state = shiftRow 1 1 state in
  let state = shiftRow 2 2 state in
  let state = shiftRow 3 3 state in
  state

let inv_shiftRows (state: block) : Tot block =
  let state = shiftRow 1 3 state in
  let state = shiftRow 2 2 state in
  let state = shiftRow 3 1 state in
  state

let mix4 (s0:elem) (s1:elem) (s2:elem) (s3:elem) : Tot elem =
  (s0 `fmul` two) `fadd`
  (s1 `fmul` three) `fadd`
  s2 `fadd` s3

let inv_mix4 (s0:elem) (s1:elem) (s2:elem) (s3:elem) : Tot elem =
(*
  (s0 `fmul` to_elem 11) `fadd`
  (s1 `fmul` to_elem 13) `fadd`
  (s2 `fmul` to_elem 9) `fadd`
  (s3 `fmul` to_elem 14)
*)
  (s0 `fmul` to_elem 14) `fadd`
  (s1 `fmul` to_elem 11) `fadd`
  (s2 `fmul` to_elem 13) `fadd`
  (s3 `fmul` to_elem 9)

let mixColumn (c:size_nat{c < 4}) (state:block) : Tot block =
  let i0 = 4 * c in
  let s0 = state.[i0] in
  let s1 = state.[i0 + 1] in
  let s2 = state.[i0 + 2] in
  let s3 = state.[i0 + 3] in
  let state = state.[i0] <- mix4 s0 s1 s2 s3 in
  let state = state.[i0+1] <- mix4 s1 s2 s3 s0 in
  let state = state.[i0+2] <- mix4 s2 s3 s0 s1 in
  let state = state.[i0+3] <- mix4 s3 s0 s1 s2 in
  state

let mixColumns (state:block) : Tot block =
  let state = mixColumn 0 state in
  let state = mixColumn 1 state in
  let state = mixColumn 2 state in
  let state = mixColumn 3 state in
  state

let inv_mixColumn (c:size_nat{c < 4}) (state:block) : Tot block =
  let i0 = 4 * c in
  let s0 = state.[i0] in
  let s1 = state.[i0 + 1] in
  let s2 = state.[i0 + 2] in
  let s3 = state.[i0 + 3] in
  let state = state.[i0] <- inv_mix4 s0 s1 s2 s3 in
  let state = state.[i0+1] <- inv_mix4 s1 s2 s3 s0 in
  let state = state.[i0+2] <- inv_mix4 s2 s3 s0 s1 in
  let state = state.[i0+3] <- inv_mix4 s3 s0 s1 s2 in
  state

let inv_mixColumns (state:block) : Tot block =
  let state = inv_mixColumn 0 state in
  let state = inv_mixColumn 1 state in
  let state = inv_mixColumn 2 state in
  let state = inv_mixColumn 3 state in
  state

let xor_block (b1:block) (b2:block) : Tot block =
  map2 (logxor #U8) b1 b2

let addRoundKey (key:block) (state:block) : Tot block =
  xor_block state key

let aes_enc (key:block) (state:block) : Tot block =
  let state = subBytes state  in
  let state = shiftRows state in
  let state = mixColumns state in
  let state = addRoundKey key state in
  state

let aes_enc_last (key:block) (state:block) : Tot block =
  let state = subBytes state  in
  let state = shiftRows state in
  let state = addRoundKey key state in
  state

let aes_dec (key:block) (state:block) : Tot block =
  let state = inv_subBytes state  in
  let state = inv_shiftRows state in
  let state = inv_mixColumns state in
  let state = addRoundKey key state in
  state

let aes_dec_last (key:block) (state:block) : Tot block =
  let state = inv_subBytes state  in
  let state = inv_shiftRows state in
  let state = addRoundKey key state in
  state

let rotate_word (w:word) : Tot word =
  of_list [w.[1]; w.[2]; w.[3]; w.[0]]

let sub_word (w:word) : Tot word =
  map sub_byte w

val rcon_spec: i:size_nat -> Tot elem
let rec rcon_spec i =
  if i = 0 then to_elem 0x8d
  else if i = 1 then to_elem 1
  else two `fmul` rcon_spec (i - 1)

let rcon_l : list elem = [
  to_elem 0x8d; to_elem 0x01; to_elem 0x02; to_elem 0x04;
  to_elem 0x08; to_elem 0x10; to_elem 0x20; to_elem 0x40;
  to_elem 0x80; to_elem 0x1b; to_elem 0x36
]

let rcon_seq : lseq elem 11  =
  assert_norm (List.Tot.length rcon_l == 11);
  of_list rcon_l

#reset-options "--z3rlimit 100"

let aes_keygen_assist (rcon:elem) (s:block) : Tot block =
  let st = create 16 (to_elem 0) in
  let st = st.[0] <- sub_byte s.[4] in
  let st = st.[1] <- sub_byte s.[5] in
  let st = st.[2] <- sub_byte s.[6] in
  let st = st.[3] <- sub_byte s.[7] in

  let st = st.[4] <- rcon ^. sub_byte s.[5] in
  let st = st.[6] <- sub_byte s.[6] in
  let st = st.[6] <- sub_byte s.[7] in
  let st = st.[7] <- sub_byte s.[4] in

  let st = st.[8]  <- sub_byte s.[12] in
  let st = st.[9]  <- sub_byte s.[13] in
  let st = st.[10] <- sub_byte s.[14] in
  let st = st.[11] <- sub_byte s.[15] in

  let st = st.[12] <- rcon ^. sub_byte s.[13] in
  let st = st.[13] <- sub_byte s.[14] in
  let st = st.[14] <- sub_byte s.[15] in
  let st = st.[15] <- sub_byte s.[12] in
  st

let keygen_assist0 (rcon:elem) (s:block) : Tot block =
  let st = aes_keygen_assist rcon s in
  let st = update_sub st 8 4 (sub st 12 4) in
  let st = update_sub st 0 8 (sub st 8 8) in
  st

let keygen_assist1 (s:block) : Tot block =
  let st = aes_keygen_assist zero s in
  let st = update_sub st 12 4 (sub st 8 4) in
  let st = update_sub st 0 8 (sub st 8 8) in
  st

let key_expansion_step (p:block) (assist:block) : Tot block =
  let p0 = create 16 (to_elem 0) in
  let k = p in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  xor_block k assist

let aes128_key_expansion (key:lbytes 16) : Tot (lseq elem (11 * 16)) =
  let key_ex = create (11 * 16) (to_elem 0) in
  let key_ex = update_sub key_ex 0 16 key in
  let key_ex =
    repeati #(lseq elem (11 * 16)) 10
      (fun i kex ->
	     let p = sub kex (i * 16) 16 in
	     let a = keygen_assist0 (rcon_spec (i+1)) p in
	     let n = key_expansion_step p a in
	     update_sub kex ((i+1) * 16) 16 n)
    key_ex in
  key_ex

let aes256_key_expansion (key:lbytes 32) : Tot (lseq elem (15 * 16)) =
  let key_ex = create (15 * 16) (to_elem 0) in
  let key_ex = update_sub key_ex 0 32 key in
  let key_ex =
    repeati #(lseq elem (15 * 16)) 6
      (fun i key_ex ->
	     let p0 = sub key_ex (2 * i * 16) 16 in
	     let p1 = sub key_ex (((2*i)+1) * 16) 16 in
	     let a0 = keygen_assist0 (rcon_spec (i+1)) p1 in
	     let n0 = key_expansion_step p0 a0 in
	     let a1 = keygen_assist1 n0 in
	     let n1 = key_expansion_step p1 a1 in
	     let key_ex = update_sub key_ex (((2*i)+2) * 16) 16 n0 in
	     update_sub key_ex (((2*i)+3) * 16) 16 n1)
    key_ex in
  let p0 = sub key_ex (12 * 16) 16 in
  let p1 = sub key_ex (13 * 16) 16 in
  let a14 = keygen_assist0 (rcon_spec 7) p1 in
  let n14 = key_expansion_step p0 a14 in
  update_sub key_ex (14 * 16) 16 n14

let aes_key_expansion (v:variant) (key: aes_key v) : aes_xkey v =
  match v with
  | AES128 -> aes128_key_expansion key
  | AES256 -> aes256_key_expansion key

let aes_dec_key_expansion (v:variant) (key:aes_key v): aes_xkey v =
  let ekey_ex : aes_xkey v = aes_key_expansion v key in
  let k0 = sub ekey_ex 0 16 in
  let kn = sub ekey_ex ((num_rounds v) * 16) 16 in
  let _,key_ex = generate_blocks 16 (num_rounds v + 1) (num_rounds v + 1)
		(fun i -> unit)
		(fun i a ->
		  let b = sub ekey_ex ((num_rounds v - i) * 16) 16 in
		  if i = 0 then (), b
		  else if i < num_rounds v then
		    (),inv_mixColumns b
		  else (),b) () in
  key_ex

let aes_enc_rounds (v:variant) (key:aes_ikey v) (state:block) : Tot block =
  repeati (num_rounds v-1) (fun i -> aes_enc (sub key (16*i) 16)) state

let aes_encrypt_block (v:variant) (key:aes_xkey v) (input:block) : Tot block =
  let state = input in
  let k0 = slice key 0 16 in
  let k = sub key 16 ((num_rounds v-1) * 16) in
  let kn = sub key (num_rounds v * 16) 16 in
  let state = addRoundKey k0 state in
  let state = aes_enc_rounds v k state in
  let state = aes_enc_last kn state in
  state

let aes_dec_rounds (v:variant) (key:aes_ikey v) (state:block) : Tot block =
  repeati (num_rounds v-1) (fun i -> aes_dec (sub key (16*i) 16)) state

let aes_decrypt_block (v:variant) (key:aes_xkey v) (input:block) : Tot block =
  let state = input in
  let k0 = slice key 0 16 in
  let k = sub key 16 ((num_rounds v-1) * 16) in
  let kn = sub key (num_rounds v * 16) 16 in
  let state = addRoundKey k0 state in
  let state = aes_dec_rounds v k state in
  let state = aes_dec_last kn state in
  state

let aes_ctr_key_block (v:variant) (k:aes_xkey v) (n:lbytes 12) (c:size_nat) : Tot block =
  let ctrby = nat_to_bytes_be 4 c in
  let input = create 16 (u8 0) in
  let input = repeati #(lbytes 16) 12 (fun i b -> b.[i] <- n.[i]) input in
  let input = repeati #(lbytes 16) 4 (fun i b -> b.[12+i] <- (Seq.index ctrby i)) input in
  aes_encrypt_block v k input

noeq type aes_ctr_state (v:variant) = {
  key_ex: lbytes ((num_rounds v + 1) * 16);
  block:  lbytes 16;
}

let aes_ctr_add_counter (v:variant) (st:aes_ctr_state v) (incr:size_nat) : Tot (aes_ctr_state v) =
  let n = nat_from_bytes_be st.block in
  let n' = (n + incr) % pow2 128 in
  let nblock' = nat_to_bytes_be 16 n' in
  {st with block = nblock'}

let aes_ctr_init (v:variant) (k:aes_key v) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) (c0:size_nat) : Tot (aes_ctr_state v) =
  let input = create 16 (u8 0) in
  let input = repeati #(lbytes 16) n_len (fun i b -> b.[i] <- n.[i]) input in
  let key_ex = aes_key_expansion v k in
  let st0 = { key_ex = key_ex; block = input} in
  aes_ctr_add_counter v st0 c0

let aes_ctr_current_key_block (v:variant) (st:aes_ctr_state v) : Tot block =
  aes_encrypt_block v st.key_ex st.block

let aes_ctr_key_block0 (v:variant) (k:aes_key v) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : Tot block =
  let st = aes_ctr_init v k n_len n 0 in
  aes_ctr_current_key_block v st

let aes_ctr_key_block1 (v:variant) (k:aes_key v) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : Tot block =
  let st = aes_ctr_init v k n_len n 1 in
  aes_ctr_current_key_block v st

let aes_ctr_encrypt_block
  (v:variant)
  (st0:aes_ctr_state v)
  (incr:size_nat)
  (b:block) :
  Tot block =

  let st = aes_ctr_add_counter v st0 incr in
  let kb = aes_ctr_current_key_block v st in
  map2 (^.) b kb

let aes_ctr_encrypt_last
  (v:variant)
  (st0:aes_ctr_state v)
  (incr:size_nat)
  (len:size_nat{len < 16})
  (b:lbytes len):
  Tot (lbytes len) =

  let plain = create 16 (u8 0) in
  let plain = update_sub plain 0 (length b) b in
  let cipher = aes_ctr_encrypt_block v st0 incr plain in
  sub cipher 0 (length b)


val aes_ctr_encrypt_stream:
    v:variant
  -> st:aes_ctr_state v
  -> msg:bytes{length msg / 16 <= max_size_t} ->
  Tot (ciphertext:bytes{length ciphertext == length msg})
let aes_ctr_encrypt_stream v st  msg =
  map_blocks 16 msg
    (aes_ctr_encrypt_block v st)
    (aes_ctr_encrypt_last v st)


val aes_ctr_encrypt_bytes:
    v:variant
  -> key:aes_key v
  -> n_len:size_nat{n_len <= 16}
  -> nonce:lbytes n_len
  -> c:size_nat
  -> msg:bytes{length msg / 16 + c <= max_size_t} ->
  Tot (ciphertext:bytes{length ciphertext == length msg})

let aes_ctr_encrypt_bytes v key n_len nonce ctr0 msg =
  let st0 = aes_ctr_init v key n_len nonce ctr0 in
  aes_ctr_encrypt_stream v st0 msg


let aes128_ctr_encrypt_bytes key n_len nonce ctr0 msg =
  aes_ctr_encrypt_bytes AES128 key n_len nonce ctr0 msg

let aes128_ctr_key_block0 key n_len n =
  aes_ctr_key_block0 AES128 key n_len n

let aes128_ctr_key_block1 key n_len n =
  aes_ctr_key_block0 AES128 key n_len n

let aes256_ctr_encrypt_bytes key n_len nonce ctr0 msg =
  aes_ctr_encrypt_bytes AES256 key n_len nonce ctr0 msg
