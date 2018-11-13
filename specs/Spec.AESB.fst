module Spec.AESB

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
let two = to_elem 2
let three = to_elem 3

(* These operations are normalized here to avoid a huge blowup in generate code size *)
let ( <<<. ) x y = normalize_term (rotate_left #U8 #SEC x y)
let ( ^. ) x y = normalize_term (logxor #U8 #SEC x y)



/// Constants and Types

type algorithm =
  | AES_128
  | AES_192
  | AES_256

let size_block = 16
let size_word = 32

type word = lseq elem 4
type block = lseq elem 16

let size_key (a:algorithm) =
  match a with
  | AES_128 -> 4 * size_word
  | AES_192 -> 6 * size_word
  | AES_256 -> 8 * size_word

let rounds (a:algorithm) =
  match a with
  | AES_128 -> 10
  | AES_192 -> 12
  | AES_256 -> 14


(* Specification of the Rijndael S-Box : *)
let sub_byte (input:elem) =
  let s = finv input in
  s ^.
  (s <<<. size 1) ^.
  (s <<<. size 2) ^.
  (s <<<. size 3) ^.
  (s <<<. size 4) ^.
  (to_elem 99)

let subBytes (state:block) : Tot block =
  map sub_byte state

let shiftRow (i:size_nat{i < 4}) (shift:size_nat{i < 4}) (state:block) : Tot block =
  let tmp0 = state.[i + (4 * (shift % 4))] in
  let tmp1 = state.[i + (4 * ((shift + 1) % 4))] in
  let tmp2 = state.[i + (4 * ((shift + 2) % 4))] in
  let tmp3 = state.[i + (4 * ((shift + 3) % 4))] in
  let state = state.[i] <- tmp0 in
  let state = state.[i + 4] <- tmp1 in
  let state = state.[i + 8] <- tmp2 in
  let state = state.[i + 12] <- tmp3 in
  state

let shiftRows (state: block) : Tot block =
  let state = shiftRow 1 1 state in
  let state = shiftRow 2 2 state in
  let state = shiftRow 3 3 state in
  state

let mix4 (s0:elem) (s1:elem) (s2:elem) (s3:elem) : Tot elem =
  (s0 `fmul` two) `fadd`
  (s1 `fmul` three) `fadd`
  s2 `fadd` s3

let mixColumn (c:size_nat{c < 4}) (state:block) : Tot block =
  let i0 = 4 * c in
  let s0 = state.[i0] in
  let s1 = state.[i0 + 1] in
  let s2 = state.[i0 + 2] in
  let s3 = state.[i0 + 3] in
  let state = state.[i0] <- mix4 s0 s1 s2 s3 in
  let state = state.[i0 + 1] <- mix4 s1 s2 s3 s0 in
  let state = state.[i0 + 2] <- mix4 s2 s3 s0 s1 in
  let state = state.[i0 + 3] <- mix4 s3 s0 s1 s2 in
  state

let mixColumns (state:block) : Tot block =
  let state = mixColumn 0 state in
  let state = mixColumn 1 state in
  let state = mixColumn 2 state in
  let state = mixColumn 3 state in
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

let aes_rounds (a:algorithm) (key:lseq elem ((rounds a - 1) * size_block)) (state:block) : Tot block =
  repeati (rounds a - 1) (fun i -> aes_enc (sub key (i * size_block) size_block)) state

let block_cipher (a:algorithm) (key:lseq elem ((rounds a + 1) * size_block)) (input:block) : Tot block =
  let state = input in
  let k0 = slice key 0 size_block in
  let k = sub key size_block ((rounds a - 1) * size_block) in
  let kn = sub key ((rounds a) * size_block) size_block in
  let state = addRoundKey k0 state in
  let state = aes_rounds a k state in
  let state = aes_enc_last kn state in
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

#reset-options "--z3rlimit 50"
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


let aes128_keygen_assist (rcon:elem) (s:block) : Tot block =
  let st = aes_keygen_assist rcon s in
  let st = update_sub st 8 4 (sub st 12 4) in
  let st = update_sub st 0 8 (sub st 8 8) in
  st

let key_expansion_step (p:block) (assist:block) : Tot block =
  let p0 = create size_block (to_elem 0) in
  let k = p in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  xor_block k assist


let aes_key_expansion (a:algorithm) (key:block) : Tot (lseq elem (((rounds a) + 1) * 16)) =
  let key_ex = create ((rounds a + 1) * 16) (to_elem 0) in
  let key_ex = repeati #(lseq elem ((rounds a + 1) * 16)) 16 (fun i kex -> kex.[i] <- key.[i]) key_ex in
  let key_ex =
    repeati #(lseq elem ((rounds a + 1) * 16)) (rounds a)
      (fun i kex ->
	     let p = sub kex (i * 16) 16 in
	     let a = aes_keygen_assist (rcon_spec (i + 1)) p in
	     let n = key_expansion_step p a in
	     update_sub kex ((i + 1) * 16) 16 n)
    key_ex in
  key_ex

let aes_block (a:algorithm) (k:block) (n:lbytes 12) (c:size_nat) : Tot block =
  let ctrby = nat_to_bytes_be 4 c in
  let input = create size_block (u8 0) in
  let input = repeati #(lbytes size_block) 12 (fun i b -> b.[i] <- n.[i]) input in
  let input = repeati #(lbytes size_block) 4 (fun i b -> b.[12+i] <- (Seq.index ctrby i)) input in
  let key_ex = aes_key_expansion a k in
  let output = block_cipher a key_ex input in
  output

let encrypt_block (a:algorithm) (k:block) (m:block) : Tot block =
  let key_ex = aes_key_expansion a k in
  let output = block_cipher a key_ex m in
  output

noeq type aes_state (a:algorithm) = {
  key_ex: lbytes ((rounds a + 1) * size_block);
  block:  lbytes size_block;
}

let aes_init (a:algorithm) (k:block) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : Tot (aes_state a) =
  let input = create size_block (u8 0) in
  let input = repeati #(lbytes size_block) n_len (fun i b -> b.[i] <- n.[i]) input in
  let key_ex = aes_key_expansion a k in
  { key_ex = key_ex; block = input}

let aes_set_counter (a:algorithm) (st:aes_state a) (c:size_nat) : Tot (aes_state a) =
  let cby = nat_to_bytes_be 4 c in
  let nblock = update_sub st.block 12 4 cby in
  {st with block = nblock}

let aes_key_block (a:algorithm) (st:aes_state a) : Tot block =
  block_cipher a st.key_ex st.block

let aes_key_block0 (a:algorithm) (k:block) (n_len:size_nat{n_len <= size_block}) (n:lbytes n_len) : Tot block =
  let st = aes_init a k n_len n in
  aes_key_block a st

let aes_key_block1 (a:algorithm) (k:block) (n_len:size_nat{n_len <= size_block}) (n:lbytes n_len) : Tot block =
  let st = aes_init a k n_len n in
  let st = aes_set_counter a st 1 in
  aes_key_block a st

let aes_encrypt_block
  (a: algorithm)
  (st0: aes_state a)
  (ctr0: size_nat)
  (incr: size_nat{ctr0 + incr <= max_size_t})
  (b:block) :
  Tot block =

  let st = aes_set_counter a st0 (ctr0 + incr) in
  let kb = aes_key_block a st in
  map2 (^.) b kb

let aes_encrypt_last
  (a: algorithm)
  (st0: aes_state a)
  (ctr0: size_nat)
  (incr: size_nat{ctr0 + incr <= max_size_t})
  (len: size_nat{len < size_block})
  (b: lbytes len):
  Tot (lbytes len) =

  let plain = create size_block (u8 0) in
  let plain = update_sub plain 0 (length b) b in
  let cipher = aes_encrypt_block a st0 ctr0 incr plain in
  sub cipher 0 (length b)


val aes_encrypt:
    a: algorithm
  -> key: lbytes size_block
  -> nonce: bytes{length nonce <= size_block}
  -> c:size_nat
  -> msg:bytes{length msg / size_block + c <= max_size_t} ->
  Tot (ciphertext:bytes{length ciphertext == length msg})

let aes_encrypt a key nonce ctr0 msg =
  let nlen = length nonce in
  let cipher = msg in
  let st0 = aes_init a key nlen nonce in
  map_blocks size_block cipher
    (aes_encrypt_block a st0 ctr0)
    (aes_encrypt_last a st0 ctr0)
