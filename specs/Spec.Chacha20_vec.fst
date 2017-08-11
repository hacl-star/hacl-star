module Spec.Chacha20_vec

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

module U32 = FStar.UInt32
(* This should go elsewhere! *)

#reset-options "--max_fuel 0 --z3rlimit 100"

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type nonce = lbytes noncelen
type counter = UInt.uint_t 32

// using @ as a functional substitute for ;
// internally, blocks are represented as 16 x 4-byte integers
type vec   = v:seq UInt32.t {length v = 4}
type state = m:seq vec      {length m = 4}
type idx = n:nat{n < 4}
type shuffle = state -> Tot state

(* unfold  *)let op_Plus_Percent_Hat (x:vec) (y:vec) : Tot vec =
       Spec.Loops.seq_map2 U32.op_Plus_Percent_Hat x y

(* unfold *) let op_Hat_Hat (x:vec) (y:vec) : Tot vec =
       Spec.Loops.seq_map2 U32.op_Hat_Hat x y

(* unfold *) let op_Less_Less_Less (x:vec) (n:UInt32.t{0 < v n /\ v n < 32}) : Tot vec =
       Spec.Loops.seq_map (fun x -> x <<< n) x

let shuffle_right (x:vec) (n:idx) : Tot vec =
        let z:nat = n in
        let x0 = index x ((0+z)%4) in
        let x1 = index x ((1+z)%4) in
        let x2 = index x ((2+z)%4) in
        let x3 = index x ((3+z)%4) in
	let x = upd x 0 x0 in
	let x = upd x 1 x1 in
	let x = upd x 2 x2 in
	let x = upd x 3 x3 in
	x

let shuffle_row (i:idx) (n:idx) (s:state) : Tot state =
       upd s i (shuffle_right (index s i) n)

val line: idx -> idx -> idx -> s:UInt32.t {0 < v s /\ v s < 32} -> st:state -> Tot state
let line a b d s m =
  let ma = index m a in let mb = index m b in let md = index m d in
  let ma = ma +%^ mb in
  let md = (md ^^  ma) <<< s in
  let m = upd m a ma in
  let m = upd m d md in
  m

let round (st:state) : Tot state =
  let st = line 0 1 3 16ul st in
  let st = line 2 3 1 12ul st in
  let st = line 0 1 3 8ul  st in
  let st = line 2 3 1 7ul  st in
  st

let shuffle_rows_0123 (st:state) : Tot state =
  let st = shuffle_row 1 1 st in
  let st = shuffle_row 2 2 st in
  let st = shuffle_row 3 3 st in
  st

let shuffle_rows_0321 (st:state) : Tot state =
  let st = shuffle_row 1 3 st in
  let st = shuffle_row 2 2 st in
  let st = shuffle_row 3 1 st in
  st

let column_round (st:state) : Tot state = round st

let diagonal_round (st:state) : Tot state =
  let st = shuffle_rows_0123 st in
  let st = round           st in
  let st = shuffle_rows_0321 st in
  st

let double_round (st:state) : Tot state =
  let st = column_round st in
  let st = diagonal_round st in
  st

let rounds (st:state) : Tot state =
    iter 10 double_round st (* 20 rounds *)

let chacha20_core (s:state) : Tot state =
    let s' = rounds s in
    Spec.Loops.seq_map2 op_Plus_Percent_Hat s' s

(* state initialization *)
unfold let constants = [0x61707865ul; 0x3320646eul; 0x79622d32ul; 0x6b206574ul]
let c0 = 0x61707865ul
let c1 = 0x3320646eul
let c2 = 0x79622d32ul
let c3 = 0x6b206574ul

// JK: I have to add those assertions to typechecks, would be nice to get rid of it
let setup (k:key) (n:nonce) (c:counter): Tot state =
  let constants : vec = Seq.Create.create_4 c0 c1 c2 c3 in
  let key_part_1:vec = uint32s_from_le 4 (Seq.slice k 0 16)  in
  let key_part_2:vec = uint32s_from_le 4 (Seq.slice k 16 32) in
  let nonce    :vec = Seq.cons (UInt32.uint_to_t c) (uint32s_from_le 3 n) in
  Seq.Create.create_4 constants key_part_1 key_part_2 nonce

let chacha20_block (k:key) (n:nonce) (c:counter): Tot block =
    let st = setup k n c in
    let st' = chacha20_core st in
    uint32s_to_le 4 (index st' 0) @|
    uint32s_to_le 4 (index st' 1) @|
    uint32s_to_le 4 (index st' 2) @|
    uint32s_to_le 4 (index st' 3)

let chacha20_ctx: Spec.CTR.block_cipher_ctx =
    let open Spec.CTR in
    {
    keylen = keylen;
    blocklen = blocklen;
    noncelen = noncelen;
    counterbits = 32;
    incr = 1
    }

let chacha20_cipher: Spec.CTR.block_cipher chacha20_ctx = chacha20_block

let chacha20_encrypt_bytes key nonce counter m =
    Spec.CTR.counter_mode chacha20_ctx chacha20_cipher key nonce counter m

#set-options "--lax"

unfold let test_plaintext = [
    0x4cuy; 0x61uy; 0x64uy; 0x69uy; 0x65uy; 0x73uy; 0x20uy; 0x61uy;
    0x6euy; 0x64uy; 0x20uy; 0x47uy; 0x65uy; 0x6euy; 0x74uy; 0x6cuy;
    0x65uy; 0x6duy; 0x65uy; 0x6euy; 0x20uy; 0x6fuy; 0x66uy; 0x20uy;
    0x74uy; 0x68uy; 0x65uy; 0x20uy; 0x63uy; 0x6cuy; 0x61uy; 0x73uy;
    0x73uy; 0x20uy; 0x6fuy; 0x66uy; 0x20uy; 0x27uy; 0x39uy; 0x39uy;
    0x3auy; 0x20uy; 0x49uy; 0x66uy; 0x20uy; 0x49uy; 0x20uy; 0x63uy;
    0x6fuy; 0x75uy; 0x6cuy; 0x64uy; 0x20uy; 0x6fuy; 0x66uy; 0x66uy;
    0x65uy; 0x72uy; 0x20uy; 0x79uy; 0x6fuy; 0x75uy; 0x20uy; 0x6fuy;
    0x6euy; 0x6cuy; 0x79uy; 0x20uy; 0x6fuy; 0x6euy; 0x65uy; 0x20uy;
    0x74uy; 0x69uy; 0x70uy; 0x20uy; 0x66uy; 0x6fuy; 0x72uy; 0x20uy;
    0x74uy; 0x68uy; 0x65uy; 0x20uy; 0x66uy; 0x75uy; 0x74uy; 0x75uy;
    0x72uy; 0x65uy; 0x2cuy; 0x20uy; 0x73uy; 0x75uy; 0x6euy; 0x73uy;
    0x63uy; 0x72uy; 0x65uy; 0x65uy; 0x6euy; 0x20uy; 0x77uy; 0x6fuy;
    0x75uy; 0x6cuy; 0x64uy; 0x20uy; 0x62uy; 0x65uy; 0x20uy; 0x69uy;
    0x74uy; 0x2euy
]

unfold let test_ciphertext = [
    0x6euy; 0x2euy; 0x35uy; 0x9auy; 0x25uy; 0x68uy; 0xf9uy; 0x80uy;
    0x41uy; 0xbauy; 0x07uy; 0x28uy; 0xdduy; 0x0duy; 0x69uy; 0x81uy;
    0xe9uy; 0x7euy; 0x7auy; 0xecuy; 0x1duy; 0x43uy; 0x60uy; 0xc2uy;
    0x0auy; 0x27uy; 0xafuy; 0xccuy; 0xfduy; 0x9fuy; 0xaeuy; 0x0buy;
    0xf9uy; 0x1buy; 0x65uy; 0xc5uy; 0x52uy; 0x47uy; 0x33uy; 0xabuy;
    0x8fuy; 0x59uy; 0x3duy; 0xabuy; 0xcduy; 0x62uy; 0xb3uy; 0x57uy;
    0x16uy; 0x39uy; 0xd6uy; 0x24uy; 0xe6uy; 0x51uy; 0x52uy; 0xabuy;
    0x8fuy; 0x53uy; 0x0cuy; 0x35uy; 0x9fuy; 0x08uy; 0x61uy; 0xd8uy;
    0x07uy; 0xcauy; 0x0duy; 0xbfuy; 0x50uy; 0x0duy; 0x6auy; 0x61uy;
    0x56uy; 0xa3uy; 0x8euy; 0x08uy; 0x8auy; 0x22uy; 0xb6uy; 0x5euy;
    0x52uy; 0xbcuy; 0x51uy; 0x4duy; 0x16uy; 0xccuy; 0xf8uy; 0x06uy;
    0x81uy; 0x8cuy; 0xe9uy; 0x1auy; 0xb7uy; 0x79uy; 0x37uy; 0x36uy;
    0x5auy; 0xf9uy; 0x0buy; 0xbfuy; 0x74uy; 0xa3uy; 0x5buy; 0xe6uy;
    0xb4uy; 0x0buy; 0x8euy; 0xeduy; 0xf2uy; 0x78uy; 0x5euy; 0x42uy;
    0x87uy; 0x4duy
]

unfold let test_key = [
    0uy;   1uy;  2uy;  3uy;  4uy;  5uy;  6uy;  7uy;
    8uy;   9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy;
    16uy; 17uy; 18uy; 19uy; 20uy; 21uy; 22uy; 23uy;
    24uy; 25uy; 26uy; 27uy; 28uy; 29uy; 30uy; 31uy
    ]
unfold let test_nonce = [
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0x4auy; 0uy; 0uy; 0uy; 0uy
    ]

unfold let test_counter = 1

let test() =
  assert_norm(List.Tot.length test_plaintext = 114);
  assert_norm(List.Tot.length test_ciphertext = 114);
  assert_norm(List.Tot.length test_key = 32);
  assert_norm(List.Tot.length test_nonce = 12);
  let test_plaintext = createL test_plaintext in
  let test_ciphertext = createL test_ciphertext in
  let test_key = createL test_key in
  let test_nonce = createL test_nonce in
  chacha20_encrypt_bytes test_key test_nonce test_counter test_plaintext
  = test_ciphertext
