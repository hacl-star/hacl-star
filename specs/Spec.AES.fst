module Spec.AES

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

(* A specificationf for bitsliced AES. No optimizations. *)

(* The GF(8) field, to be used to prove that the bitsliced spec implements AES:

   let gf8 = mk_field 8 0xd8
   let elem = felem gf8
   let to_elem a = to_felem #gf8 (uint_to_nat #U8 a)
   let from_elem a = u8 (from_felem #gf8 a)
   let zero = zero #gf8
   let two = to_elem (u8 2)
   let three = to_elem (u8 3)
   let fadd a b = fadd #gf8 a b
   let fmul a b = fmul #gf8 a b
   let finv a = finv #gf8 (to_elem (u8 0x1b)) a
*)

(* Specialized imlplementation of GF(8) field *)

let elem = uint8
let to_elem x = x
let from_elem x = x
let zero = u8 0

type word = lbytes 4
type block = lbytes 16

(* let fadd (a:uint8) (b:uint8) : uint8 = a ^. b *)

let fmul (a:uint8) (b:uint8) : uint8 =
  let (p,a,b) =
    repeati 7 (fun i (p,a,b) ->
	   let b0 = eq_mask #U8 (b &. u8 1) (u8 1) in
	   let p = p ^. (b0 &. a) in
  	   let carry_mask = gte_mask #U8 a (u8 0x80) in
	   let a = a <<. size 1 in
	   let a = a ^. (carry_mask &. u8 0x1b) in
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
let sbox input =
  let s = finv input in
  let r: uint8 = logxor #U8 s ((s <<<. size 1) ^. (s <<<. size 2) ^. (s <<<. size 3) ^. (s <<<. size 4) ^. (u8 99)) in
  r

let subBytes (state:block) : block =
  map sbox state

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

(* SPEC for mixColumn: broken, to fix, to prove:
let mixColumn (c:size_nat{c < 4}) (state:block) : block =
  let i0 = 4 * c in
  let s0 = to_elem state.[i0] in
  let s1 = to_elem state.[i0 + 1] in
  let s2 = to_elem state.[i0 + 2] in
  let s3 = to_elem state.[i0 + 3] in
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
*)

let xtime (x:uint8) : uint8 =
  let x1 : uint8 = shift_left #U8 x (size 1) in
  let x7 : uint8 = shift_right #U8 x (size 7) in
  let x71 : uint8 = logand #U8 x7 (u8 1) in
  let x711b : uint8 = mul_mod #U8 x71 (u8 0x1b) in
  logxor #U8 x1 x711b

let mixColumn (c:size_nat{c < 4}) (state:block) : block =
  let i0 = 4 * c in
  let s0 : uint8 = state.[i0] in
  let s1 : uint8 = state.[i0 + 1] in
  let s2 : uint8 = state.[i0 + 2] in
  let s3 : uint8 = state.[i0 + 3] in
  let tmp : uint8 = logxor #U8 s0 (s1 ^. s2 ^. s3) in
  let state = state.[i0] <- logxor #U8 s0 (tmp ^. (xtime (logxor #U8 s0 s1))) in
  let state = state.[i0+1] <- logxor #U8 s1 (tmp ^. (xtime (logxor #U8 s1 s2))) in
  let state = state.[i0+2] <- logxor #U8 s2 (tmp ^. (xtime (logxor #U8 s2 s3))) in
  let state = state.[i0+3] <- logxor #U8 s3 (tmp ^. (xtime (logxor #U8 s3 s0))) in
  state

let mixColumns (state:block) : block =
  let state = mixColumn 0 state in
  let state = mixColumn 1 state in
  let state = mixColumn 2 state in
  let state = mixColumn 3 state in
  state

let addRoundKey (key:block) (state:block) : block =
  map2 (logxor #U8) state key

let round (key:block) (state:block) =
  let state = subBytes state  in
  let state = shiftRows state in
  let state = mixColumns state in
  let state = addRoundKey key state in
  state

let rounds (key:lbytes (9 * 16)) (state:block) =
  repeati 9 (fun i -> round (sub key (16*i) 16)) state

let block_cipher (key:lbytes (11 * 16)) (input:block) =
  let state = input in
  let k0 = slice key 0 16 in
  let k = sub key 16 (9 * 16) in
  let kn = sub key (10 * 16) 16 in
  let state = addRoundKey k0 state in
  let state = rounds k state in
  let state = subBytes state in
  let state = shiftRows state in
  let state = addRoundKey kn state in
  state

let rotate_word (w:word) : word =
  of_list [w.[1];w.[2];w.[3];w.[0]]

let sub_word (w:word) : word =
  map sbox w

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

let key_expansion_word (w0:word) (w1:word) (i:size_nat{i < 44}) : word =
  let k = w1 in
  let k =
    if (i % 4 = 0) then (
      let k = rotate_word k in
      let k = sub_word k in
      let rcon_i = rcon.[i / 4] in
      let k = k.[0] <- logxor #U8 rcon_i k.[0] in
      k)
    else k in
  let k = map2 (logxor #U8) w0 k in
  k

let key_expansion (key:block) : (lbytes (11 * 16)) =
  let key_ex = create (11 * 16) (u8 0) in
  let key_ex = repeati #(lbytes (11 * 16)) 16 (fun i s -> s.[i] <- key.[i]) key_ex in
  let key_ex =
    repeat_range #(lbytes (11 * 16)) 4 44
	 (fun i k -> update_slice k (i*4) ((i*4) + 4)
			    (key_expansion_word
			    (sub k ((i-4) * 4) 4)
			    (sub k ((i-1) * 4) 4)
			    i)) key_ex in
  key_ex

let aes128_block (k:block) (n:lbytes 12) (c:size_nat) : block =
  let ctrby = nat_to_bytes_be 4 c in
  let input = create 16 (u8 0) in
  let input = repeati #(lbytes 16) 12 (fun i b -> b.[i] <- n.[i]) input in
  let input = repeati #(lbytes 16) 4 (fun i b -> b.[12+i] <- (Seq.index ctrby i)) input in
  let key_ex = key_expansion k in
  let output = block_cipher key_ex input in
  output

let aes128_encrypt_block (k:block) (m:block) : block =
  let key_ex = key_expansion k in
  let output = block_cipher key_ex m in
  output

noeq type aes_state = {
  key_ex: lbytes (11 * 16);
  block:  lbytes 16;
}

let aes_init (k:block) (n_len:size_nat{n_len <= 16}) (n:lbytes n_len) : aes_state =
  let input = create 16 (u8 0) in
  let input = repeati #(lbytes 16) n_len (fun i b -> b.[i] <- n.[i]) input in
  let key_ex = key_expansion k in
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
