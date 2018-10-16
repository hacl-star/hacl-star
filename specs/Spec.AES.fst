module Spec.AES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

(* Specialized imlplementation of GF(8) field *)

let elem = uint8
let to_elem x = x
let from_elem x = x
let zero = u8 0
let two = u8 2
let three = u8 3
let irred = u8 0x1b 
type word = lbytes 4
type block = lbytes 16

let fadd (a:uint8) (b:uint8) : uint8 = a ^. b 

let fmul (a:uint8) (b:uint8) : uint8 =
  let (p,a,b) =
    repeati 7 (fun i (p,a,b) ->
	   let b0 = eq_mask #U8 (b &. u8 1) (u8 1) in
	   let p = p ^. (b0 &. a) in
  	   let carry_mask = gte_mask #U8 a (u8 0x80) in
	   let a = a <<. size 1 in
	   let a = a ^. (carry_mask &. irred ) in
	   let b = b >>. size 1 in
	   (p,a,b)) (u8 0,a,b) in
  let b0 = eq_mask #U8 (b &. u8 1) (u8 1) in
  let p = p ^. (b0 &. a) in
  p

let finv (a: uint8) =
  let a2 = fmul a a in
  let a4 = fmul a2 a2 in
  let a8 = fmul a4 a4 in
  let a16 = fmul a8 a8 in
  let a32 = fmul a16 a16 in
  let a64 = fmul a32 a32 in
  let a128 = fmul a64 a64 in
  let a192 = fmul a128 a64 in
  let a224 = fmul a192 a32 in
  let a240 = fmul a224 a16 in
  let a248 = fmul a240 a8 in
  let a252 = fmul a248 a4 in
  let a254 = fmul a252 a2 in
  a254

(* Specification of the Rijndael S-Box : *)

let sub_byte input =
  let s = finv input in
  let r: uint8 = s ^. ((s <<<. size 1) ^. (s <<<. size 2) ^. (s <<<. size 3) ^. (s <<<. size 4) ^. (u8 99)) in
  r

let subBytes (state:block) : block =
  map sub_byte state

let shiftRow (i:size_nat{i < 4}) (shift:size_nat{i < 4}) (state:block) : block =
  let tmp0 = state.[i + (4 * (shift % 4))] in
  let tmp1 = state.[i + (4 * ((shift + 1) % 4))] in
  let tmp2 = state.[i + (4 * ((shift + 2) % 4))] in
  let tmp3 = state.[i + (4 * ((shift + 3) % 4))] in
  let state = state.[i] <- tmp0 in
  let state = state.[i+4] <- tmp1 in
  let state = state.[i+8] <- tmp2 in
  let state = state.[i+12] <- tmp3 in
  state

let shiftRows (state:block) =
  let state = shiftRow 1 1 state in
  let state = shiftRow 2 2 state in
  let state = shiftRow 3 3 state in
  state

(* SPEC for mixColumn: broken, to fix, to prove: *)

let mixColumn (c:size_nat{c < 4}) (state:block) : block =
  let i0 = 4 * c in
  let s0 = state.[i0] in
  let s1 = state.[i0 + 1] in
  let s2 = state.[i0 + 2] in
  let s3 = state.[i0 + 3] in
  let state = state.[i0] <- from_elem
			   ((s0 `fmul` two) `fadd`
			    (s1 `fmul` three) `fadd`
			     s2 `fadd` s3) in
  let state = state.[i0+1] <- from_elem
			   ((s1 `fmul` two) `fadd`
			    (s2 `fmul` three) `fadd`
			     s3 `fadd` s0) in
  let state = state.[i0+2] <- from_elem
			   ((s2 `fmul` two) `fadd`
			    (s3 `fmul` three) `fadd`
			     s0 `fadd` s1) in
  let state = state.[i0+3] <- from_elem
			   ((s3 `fmul` two) `fadd`
			    (s0 `fmul` three) `fadd`
			     s1 `fadd` s2) in
  state

let mixColumns (state:block) : block =
  let state = mixColumn 0 state in
  let state = mixColumn 1 state in
  let state = mixColumn 2 state in
  let state = mixColumn 3 state in
  state

let xor_block (b1:block) (b2:block) : block =
  map2 (logxor #U8) b1 b2

let addRoundKey (key:block) (state:block) : block =
  xor_block state key

let aes_enc (key:block) (state:block) =
  let state = subBytes state  in
  let state = shiftRows state in
  let state = mixColumns state in
  let state = addRoundKey key state in
  state

let aes_enc_last (key:block) (state:block) =
  let state = subBytes state  in
  let state = shiftRows state in
  let state = addRoundKey key state in
  state

let rounds (key:lbytes (9 * 16)) (state:block) =
  repeati 9 (fun i -> aes_enc(sub key (16*i) 16)) state

let block_cipher (key:lbytes (11 * 16)) (input:block) =
  let state = input in
  let k0 = slice key 0 16 in
  let k = sub key 16 (9 * 16) in
  let kn = sub key (10 * 16) 16 in
  let state = addRoundKey k0 state in
  let state = rounds k state in
  let state = aes_enc_last kn state in
  state

let rotate_word (w:word) : word =
  of_list [w.[1];w.[2];w.[3];w.[0]]

let sub_word (w:word) : word =
  map sub_byte w

(*
SPEC for rcon: broken? to fix, to prove.
val rcon_spec: i:size_nat{i >= 1} -> elem
let rec rcon_spec i =
  if i = 1 then to_elem (u8 1)
  else two `fmul` rcon_spec (i - 1)
*)

let rcon_l : list uint8 = [
  u8 0x8d; u8 0x01; u8 0x02; u8 0x04;
  u8 0x08; u8 0x10; u8 0x20; u8 0x40;
  u8 0x80; u8 0x1b; u8 0x36
]

let rcon : lbytes 11 =
  assert_norm (List.Tot.length rcon_l = 11);
  of_list #uint8 rcon_l

let aes_keygen_assist (rcon:uint8) (s:block) : block =
  let st = create 16 (u8 0) in
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

(*
let aes_keygen_assist (rcon:uint8) (s:block) : block =
  let st = create 16 (u8 0) in
  let st = st.[0] <- rcon ^. sub_byte s.[1] in
  let st = st.[1] <- sub_byte s.[2] in
  let st = st.[2] <- sub_byte s.[3] in
  let st = st.[3] <- sub_byte s.[0] in

  let st = st.[4] <- sub_byte s.[0] in
  let st = st.[6] <- sub_byte s.[1] in
  let st = st.[6] <- sub_byte s.[2] in
  let st = st.[7] <- sub_byte s.[3] in

  let st = st.[8]  <- rcon ^. sub_byte s.[8] in
  let st = st.[9]  <- sub_byte s.[9] in
  let st = st.[10] <- sub_byte s.[10] in
  let st = st.[11] <- sub_byte s.[11] in

  let st = st.[12] <- sub_byte s.[12] in
  let st = st.[13] <- sub_byte s.[13] in
  let st = st.[14] <- sub_byte s.[14] in
  let st = st.[15] <- sub_byte s.[15] in
  st

let aes128_keygen_assist (rcon:uint8) (s:block) : block =
  let st = aes_keygen_assist rcon s in
  let st = update_sub st 4 4 (sub st 0 4) in
  let st = update_sub st 8 8 (sub st 0 8) in
  st*)


let aes128_keygen_assist (rcon:uint8) (s:block) : block =
  let st = aes_keygen_assist rcon s in
  let st = update_sub st 8 4 (sub st 12 4) in
  let st = update_sub st 0 8 (sub st 8 8) in
  st
  
let key_expansion_step (p:block) (assist:block) : block = 
  let p0 = create 16 (u8 0) in
  let k = p in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  let k = xor_block k (update_sub p0 4 12 (sub k 0 12)) in
  xor_block k assist

let aes128_key_expansion (key:block) : (lbytes (11 * 16)) =
  let key_ex = create (11 * 16) (u8 0) in
  let key_ex = repeati #(lbytes (11 * 16)) 16 (fun i kex -> kex.[i] <- key.[i]) key_ex in
  let key_ex =
    repeati #(lbytes (11 * 16)) 10
      (fun i kex -> 
	let p = sub kex (i * 16) 16 in
	let a = aes128_keygen_assist rcon.[i+1] p in
	let n = key_expansion_step p a in
	update_sub kex ((i+1) * 16) 16 n)
    key_ex in
  key_ex

let aes128_block (k:block) (n:lbytes 12) (c:size_nat) : block =
  let ctrby = nat_to_bytes_be 4 c in
  let input = create 16 (u8 0) in
  let input = repeati #(lbytes 16) 12 (fun i b -> b.[i] <- n.[i]) input in
  let input = repeati #(lbytes 16) 4 (fun i b -> b.[12+i] <- (Seq.index ctrby i)) input in
  let key_ex = aes128_key_expansion k in
  let output = block_cipher key_ex input in
  output

let aes128_encrypt_block (k:block) (m:block) : block =
  let key_ex = aes128_key_expansion k in
  let output = block_cipher key_ex m in
  output

noeq type aes_state = {
  key_ex: lbytes (11 * 16);
  block:  lbytes 16;
}

let aes_init (k:block) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : aes_state =
  let input = create 16 (u8 0) in
  let input = repeati #(lbytes 16) n_len (fun i b -> b.[i] <- n.[i]) input in
  let key_ex = aes128_key_expansion k in
  { key_ex = key_ex; block = input}

let aes_set_counter (st:aes_state) (c:size_nat) : aes_state =
  let cby = nat_to_bytes_be 4 c in
  let nblock = update_sub st.block 12 4 cby in
  {st with block = nblock}

let aes_key_block (st:aes_state) : block =
  block_cipher st.key_ex st.block

let aes_key_block0 (k:block) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : block =
  let st = aes_init k n_len n in
  aes_key_block st

let aes_key_block1 (k:block) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : block =
  let st = aes_init k n_len n in
  let st = aes_set_counter st 1 in
  aes_key_block st

let aes_encrypt_block (st0:aes_state) (ctr0:size_nat) (incr:size_nat{ctr0 + incr <= max_size_t}) (b:block) : block =
  let st = aes_set_counter st0 (ctr0 + incr) in
  let kb = aes_key_block st in
  map2 (^.) b kb

let aes_encrypt_last
  (st0:aes_state)
  (ctr0:size_nat)
  (incr:size_nat{ctr0 + incr <= max_size_t})
  (len:size_nat{len < 16})
  (b:lbytes len): lbytes len =
  let plain = create 16 (u8 0) in
  let plain = update_sub plain 0 (length b) b in
  let cipher = aes_encrypt_block st0 ctr0 incr plain in
  sub cipher 0 (length b)


val aes128_encrypt_bytes:
    key:block
  -> n_len:size_nat{n_len <= 16}
  -> nonce:lbytes n_len
  -> c:size_nat
  -> msg:bytes{length msg / 16 + c <= max_size_t}
  -> cipher:bytes{length cipher == length msg}

let aes128_encrypt_bytes key n_len nonce ctr0 msg =
  let cipher = msg in
  let st0 = aes_init key n_len nonce in
  map_blocks 16 cipher
    (aes_encrypt_block st0 ctr0)
    (aes_encrypt_last st0 ctr0)
