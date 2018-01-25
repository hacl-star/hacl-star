module Spec.AES

open FStar.Mul
open Spec.GaloisField
open FStar.Seq
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open Spec.Lib.IntSeq

let gf8 = mk_field 8 0xd8
let elem = felem gf8
let zero = zero #gf8
let to_elem a = to_felem #gf8 (uint_to_nat #U8 a)
let from_elem a = u8 (from_felem #gf8 a)


let two = to_elem (u8 2)
let three = to_elem (u8 3)


let fadd a b = fadd #gf8 a b 
let fmul a b = fmul #gf8 a b 
let finv a = finv #gf8 (to_elem (u8 0x1b)) a


val sbox: n:uint8 -> uint8
let sbox input = 
  let a = to_elem input in
  let a' = finv a in
  let s = from_elem a' in
  let r: uint8 = logxor #U8 s ((s <<<. u32 1) ^. (s <<<. u32 2) ^. (s <<<. u32 3) ^. (s <<<. u32 4) ^. (u8 99)) in
  r

type block = lseq uint8 16 

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

(*
SPEC for mixColumn: broken, to fix, to prove.
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
  let x1 : uint8 = shift_left #U8 x (u32 1) in
  let x7 : uint8 = shift_right #U8 x (u32 7) in
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

let rounds (key:lseq uint8 (9 * 16)) (state:block) =
  repeati 9 (fun i -> round (sub key (16*i) 16)) state

let block_cipher (key:lseq uint8 (11 * 16)) (input:block) =
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

type word = lseq uint8 4 
let rotate_word (w:word) : word = 
  createL [w.[1];w.[2];w.[3];w.[0]]

let sub_word (w:word) : word =
  map sbox w

let rcon_l = [u8 0x8d; u8 0x01; u8 0x02; u8 0x04; u8 0x08; u8 0x10; u8 0x20; u8 0x40; u8 0x80; u8 0x1b; u8 0x36]

let rcon : lseq uint8 11 = 
  assert_norm (List.Tot.length rcon_l = 11);
  createL #uint8 rcon_l

(*
SPEC for rcon: broken? to fix, to prove.
val rcon_spec: i:size_nat{i >= 1} -> elem
let rec rcon_spec i = 
  if i = 1 then to_elem (u8 1)
  else two `fmul` rcon_spec (i - 1)
*)

let key_expansion_word (w0:word) (w1:word) (i:size_nat{i < 48}) : word = 
  let k = w1 in
  let k = 
    if (i % 4 = 0) then 
       let k = rotate_word k in
       let k = sub_word k in
       let rcon_i = rcon.[i / 4] in
       let k = k.[0] <- logxor #U8 rcon_i k.[0] in
       k
    else k in
  let k = map2 (logxor #U8) w0 k in
  k

let key_expansion (key:block) : (lseq uint8 (11 * 16)) = 
  let key_ex = create (11 * 16) (u8 0) in
  let key_ex = repeati 16 (fun i s -> s.[i] <- key.[i]) key_ex in
  let key_ex = repeat_range 4 44
		       (fun i k -> update_slice k (i*4) ((i*4) + 4) 
			(key_expansion_word 
			  (sub k ((i-4) * 4) 4)
			  (sub k ((i-1) * 4) 4)
			  i))
		       key_ex in
  key_ex


let aes128_block (k:block) (n:lseq uint8 12) (c:size_nat) : block = 
  let ctrby = nat_to_bytes_be 4 c in
  let input = create 16 (u8 0) in
  let input = repeati 12 (fun i b -> b.[i] <- n.[i]) input in 
  let input = repeati 4 (fun i b -> b.[12+i] <- ctrby.[i]) input in 
  let key_ex = key_expansion k in
  let output = block_cipher key_ex input in
  output

noeq type aes_state = {
  key_ex: lseq uint8 (11 `op_Multiply` 16);
  block:  lseq uint8 16;
}

let aes_init (k:block) (n:lseq uint8 12) : aes_state = 
  let input = create 16 (u8 0) in
  let input = repeati 12 (fun i b -> b.[i] <- n.[i]) input in 
  let key_ex = key_expansion k in
  {key_ex = key_ex;
   block  = input}

let aes_set_counter (st:aes_state) (c:size_nat) : Tot aes_state = 
  let ctrby = nat_to_bytes_be 4 c in
  let input = repeati 4 (fun i b -> b.[12+i] <- ctrby.[i]) st.block in 
  {st with block = input}

let aes_key_block (st:aes_state) : Tot block = 
  block_cipher st.key_ex st.block

let aes_key_block0 (k:block) (n:lseq uint8 12) : Tot block = 
  let st = aes_init k n in
  aes_key_block st

let aes128_cipher =
  Spec.CTR.Cipher aes_state 16 12 max_size_t 16 aes_init aes_set_counter aes_key_block

let aes128_encrypt_bytes key nonce counter n m = 
  Spec.CTR.counter_mode aes128_cipher key nonce counter n m

  
     
(* 

type vec = v:seq elem{length v = 4}
type block = b:seq elem{length b = 16}
type epdkey = k:seq elem{length k = 240}

type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type key = k:bytes{length k = 32}


#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val reverse: #a:Type -> s:seq a -> Tot (r:seq a{length s = length r /\
  (forall (i:nat{i < length s}). index s i == index r (length r - i - 1))})
  (decreases (length s))
let rec reverse #a s =
  if length s = 0 then createEmpty
  else begin
    let ans = snoc (reverse (tail s)) (head s) in
    assert(forall (i:nat{i < length s - 1}). index s (i + 1) == index ans (length s - 1 - i - 1));
    assert(forall (i:nat{i > 0 /\ i < length s}). index s i == index s ((i - 1) + 1));
    ans
  end

let rev_elem (e:elem) : elem = reverse e
let to_elem (u:UInt8.t) : elem = reverse (to_vec (UInt8.v u))
let from_elem (e:elem) : UInt8.t = UInt8.uint_to_t (from_vec (reverse e))

let pad (w:word) : Tot word_16 = w @| (create (16 - length w) 0uy)
let encode (w:word) : Tot block = Spec.Loops.seq_map to_elem (pad w)
let decode (e:block) : Tot word_16 = Spec.Loops.seq_map from_elem e


let rotate (s:vec) (i:nat{i < 4}) = slice s i 4 @| slice s 0 i

let shift (a:block) (r:nat{r < 4}) (i:nat{i < 4}) : block =
  let res = a in
  let res = upd res (r +  0) (index a ((r +  0 + i * 4) % 16)) in
  let res = upd res (r +  4) (index a ((r +  4 + i * 4) % 16)) in
  let res = upd res (r +  8) (index a ((r +  8 + i * 4) % 16)) in
  let res = upd res (r + 12) (index a ((r + 12 + i * 4) % 16)) in
  res

let dot (s1:vec) (s2:vec) : elem =
  (index s1 0 `fmul` index s2 0) `fadd`
  (index s1 1 `fmul` index s2 1) `fadd`
  (index s1 2 `fmul` index s2 2) `fadd`
  (index s1 3 `fmul` index s2 3)
  
let matdot (m:block) (s:vec) : vec =
  let res = create 4 zero in
  let res = upd res 0 (dot (slice m  0  4) s) in
  let res = upd res 1 (dot (slice m  4  8) s) in
  let res = upd res 2 (dot (slice m  8 12) s) in
  let res = upd res 3 (dot (slice m 12 16) s) in
  res

let mixmat : block = Spec.Loops.seq_map to_elem
  (createL [2uy; 3uy; 1uy; 1uy;
            1uy; 2uy; 3uy; 1uy;
	    1uy; 1uy; 2uy; 3uy;
	    3uy; 1uy; 1uy; 2uy])
let invmixmat : block = Spec.Loops.seq_map to_elem
  (createL [14uy; 11uy; 13uy;  9uy;
             9uy; 14uy; 11uy; 13uy;
	    13uy;  9uy; 14uy; 11uy;
	    11uy; 13uy;  9uy; 14uy])

let getSbox (e:elem) : elem = rev_elem (sbox (rev_elem e))
let getinvSbox (e:elem) : elem = rev_elem (inv_sbox (rev_elem e))


let rec rcon (i:pos) : elem =
  if i = 1 then to_elem 1uy
  else (to_elem 2uy) `fmul` rcon (i - 1)

let keyScheduleCore (s:vec) (i:pos) : vec =
  let res = rotate s 1 in
  let res = Spec.Loops.seq_map getSbox res in
  let res = upd res 0 (index res 0 `fadd` rcon i) in
  res

val keyExpansion_aux: k:seq elem{length k >= 32 /\ length k <= 240 /\ length k % 4 = 0} ->
  Tot (r:seq elem{length k + length r = 240}) (decreases (240 - length k))
let rec keyExpansion_aux k =
  let t : (v:seq elem{length v = 4}) = slice k (length k - 4) (length k) in
  let d : (v:seq elem{length v = 4}) = slice k (length k - 32) (length k - 28) in
  if length k > 236 then (assert(length k = 240); createEmpty)
  else if length k % 32 = 0 then
    let t = keyScheduleCore t (length k / 32) in
    let t = Spec.Loops.seq_map2 op_Plus_At t d in
    t @| keyExpansion_aux (k @| t)
  else if length k % 32 = 16 then
    let t = Spec.Loops.seq_map getSbox t in
    let t = Spec.Loops.seq_map2 op_Plus_At t d in
    t @| keyExpansion_aux (k @| t)
  else
    let t = Spec.Loops.seq_map2 op_Plus_At t d in
    t @| keyExpansion_aux (k @| t)
 
let keyExpansion (k:key) : epdkey =
  let ek = Spec.Loops.seq_map to_elem k in
  ek @| keyExpansion_aux ek


let addRoundKey (a:block) (k:block) : block = Spec.Loops.seq_map2 op_Plus_At a k

let shiftRows (a:block) : block =
  let a = shift a 0 0 in
  let a = shift a 1 1 in
  let a = shift a 2 2 in
  let a = shift a 3 3 in
  a
let invShiftRows (a:block) : block =
  let a = shift a 0 0 in
  let a = shift a 1 3 in
  let a = shift a 2 2 in
  let a = shift a 3 1 in
  a

let subBytes (a:block) : block = Spec.Loops.seq_map getSbox a
let invSubBytes (a:block) : block = Spec.Loops.seq_map getinvSbox a

let mixColumns (a:block) : block =
  matdot mixmat (slice a  0  4) @|
  matdot mixmat (slice a  4  8) @|
  matdot mixmat (slice a  8 12) @|
  matdot mixmat (slice a 12 16)
let invMixColumns (a:block) : block =
  matdot invmixmat (slice a  0  4) @|
  matdot invmixmat (slice a  4  8) @|
  matdot invmixmat (slice a  8 12) @|
  matdot invmixmat (slice a 12 16)

let rec cipher_loop (a:block) (k:epdkey) (i:nat{i <= 14}) : Tot block (decreases (14 - i)) =
  if i = 14 then a else
  let a = subBytes a in
  let a = shiftRows a in
  let a = mixColumns a in
  let bk : block = slice k (i * 16) (i * 16 + 16) in
  let a = addRoundKey a bk in
  cipher_loop a k (i + 1)

let cipher (w:word) (k:key) : word_16 =
  let a = encode w in
  let k = keyExpansion k in
  let a = addRoundKey a (slice k 0 16) in
  let a = cipher_loop a k 1 in
  let a = subBytes a in
  let a = shiftRows a in
  let a = addRoundKey a (slice k 224 240) in
  decode a

let rec inv_cipher_loop (a:block) (k:epdkey) (i:nat{i < 14}) : Tot block (decreases i) =
  if i = 0 then a else
  let bk : block = slice k (i * 16) (i * 16 + 16) in
  let a = addRoundKey a bk in
  let a = invMixColumns a in
  let a = invShiftRows a in
  let a = invSubBytes a in
  inv_cipher_loop a k (i - 1)

let inv_cipher (w:word) (k:key) : word_16 =
  let a = encode w in
  let k = keyExpansion k in
  let a = addRoundKey a (slice k 224 240) in
  let a = invShiftRows a in
  let a = invSubBytes a in
  let a = inv_cipher_loop a k 13 in
  let a = addRoundKey a (slice k 0 16) in
  decode a


let msg : word = createL [
  0x00uy; 0x11uy; 0x22uy; 0x33uy; 0x44uy; 0x55uy; 0x66uy; 0x77uy;
  0x88uy; 0x99uy; 0xaauy; 0xbbuy; 0xccuy; 0xdduy; 0xeeuy; 0xffuy ]

let k : key = createL [
  0x00uy; 0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy;
  0x08uy; 0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy;
  0x10uy; 0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy;
  0x18uy; 0x19uy; 0x1auy; 0x1buy; 0x1cuy; 0x1duy; 0x1euy; 0x1fuy ]

let expected : word = createL [
  0x8euy; 0xa2uy; 0xb7uy; 0xcauy; 0x51uy; 0x67uy; 0x45uy; 0xbfuy;
  0xeauy; 0xfcuy; 0x49uy; 0x90uy; 0x4buy; 0x49uy; 0x60uy; 0x89uy
]
  
let test_block() = Spec.Sbox.test() && cipher msg k = expected && inv_cipher expected k = msg


type nonce = lbytes 12
type counter = uint_t 32

let aes256_block (k:key) (n:nonce) (c:counter) : Tot word_16 =
  cipher (n @| big_bytes 4ul c) k

let aes256_ctx: Spec.CTR.block_cipher_ctx =
  let open Spec.CTR in
  {
  keylen = 32;
  blocklen = 16;
  noncelen = 12;
  counterbits = 32;
  incr = 1
  }

let aes256_cipher: Spec.CTR.block_cipher aes256_ctx = aes256_block

let aes256_encrypt_bytes key nonce counter m =
  Spec.CTR.counter_mode aes256_ctx aes256_cipher key nonce counter m


let test_plaintext : lbytes 60 = createL [
  0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy;
  0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy;
  0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy;
  0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy;
  0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy;
  0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy;
  0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy;
  0xbauy; 0x63uy; 0x7buy; 0x39uy ]

let test_ciphertext : lbytes 60 = createL [
  0x52uy; 0x2duy; 0xc1uy; 0xf0uy; 0x99uy; 0x56uy; 0x7duy; 0x07uy;
  0xf4uy; 0x7fuy; 0x37uy; 0xa3uy; 0x2auy; 0x84uy; 0x42uy; 0x7duy;
  0x64uy; 0x3auy; 0x8cuy; 0xdcuy; 0xbfuy; 0xe5uy; 0xc0uy; 0xc9uy;
  0x75uy; 0x98uy; 0xa2uy; 0xbduy; 0x25uy; 0x55uy; 0xd1uy; 0xaauy;
  0x8cuy; 0xb0uy; 0x8euy; 0x48uy; 0x59uy; 0x0duy; 0xbbuy; 0x3duy;
  0xa7uy; 0xb0uy; 0x8buy; 0x10uy; 0x56uy; 0x82uy; 0x88uy; 0x38uy;
  0xc5uy; 0xf6uy; 0x1euy; 0x63uy; 0x93uy; 0xbauy; 0x7auy; 0x0auy;
  0xbcuy; 0xc9uy; 0xf6uy; 0x62uy ]

let test_key : Spec.CTR.key aes256_ctx = createL [
  0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy;
  0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy;
  0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy;
  0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ]

let test_nonce : Spec.CTR.nonce aes256_ctx = createL [
  0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy;
  0xdeuy; 0xcauy; 0xf8uy; 0x88uy ]

let test_counter : Spec.CTR.counter aes256_ctx = 2

let test_ctr() = aes256_encrypt_bytes test_key test_nonce test_counter test_plaintext = test_ciphertext


let test() = test_block() && test_ctr()
*)
