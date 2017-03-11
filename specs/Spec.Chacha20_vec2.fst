module Spec.Chacha20_vec2

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

module U32 = FStar.UInt32
(* This should go elsewhere! *)

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type nonce = lbytes noncelen
type counter = UInt.uint_t 32

// What we need to know about vectors:
type vec   = v:seq UInt32.t {length v = 8}
let to_vec (x:U32.t) : vec = create 8 x
type state = m:seq vec      {length m = 16}
type idx = n:nat{n < 4}
type shuffle = state -> Tot state 


// Vector size changes the blocksize and the counter step:
type vec_block = lbytes (8*blocklen)
unfold let counter_step:vec  = to_vec 8ul
unfold let initial_counter : vec = 
       let l = [0ul; 1ul; 2ul; 3ul; 4ul; 5ul; 6ul; 7ul] in
       assert_norm(List.Tot.length l = 8); 
       let s = createL l in
       s       
//Transposed state matrix
type stateT = m:seq (r:seq U32.t{length r = 16}){length m = 8}

//Chacha20 code begins

unfold let op_Plus_Percent_Hat (x:vec) (y:vec) : Tot vec = 
       Combinators.seq_map2 U32.op_Plus_Percent_Hat x y

unfold let op_Hat_Hat (x:vec) (y:vec) : Tot vec = 
       Combinators.seq_map2 U32.op_Hat_Hat x y

unfold let op_Less_Less_Less (x:vec) (n:UInt32.t{v n < 32}) : Tot vec = 
       Combinators.seq_map (fun x -> x <<< n) x 

val line: idx -> idx -> idx -> s:UInt32.t {v s < 32} -> shuffle
let line a b d s m = 
  let m = upd m a (index m a +%^ index m b) in
  let m = upd m d ((index m d ^^  index m a) <<< s) in
  m

let column_round : shuffle =
  line 0 8 12 16ul @
  line 1 9 13 16ul @
  line 2 10 14 16ul @
  line 3 11 15 16ul @

  line 8 12 4 12ul @
  line 9 13 5 12ul @
  line 10 14 6 12ul @
  line 11 15 7 12ul @

  line 0 8 12 8ul @
  line 1 9 13 8ul @
  line 2 10 14 8ul @
  line 3 11 15 8ul @

  line 8 12 4 7ul @
  line 9 13 5 7ul @
  line 10 14 6 7ul @
  line 11 15 7 7ul 

let diagonal_round : shuffle =
  line 0 5 15 16ul @
  line 1 6 12 16ul @
  line 2 7 13 16ul @
  line 3 4 14 16ul @

  line 10 15 5 12ul @
  line 11 12 6 12ul @
  line 8 13 7 12ul @
  line 9 14 4 12ul @

  line 0 5 15 8ul @
  line 1 6 12 8ul @
  line 2 7 13 8ul @
  line 3 4 14 8ul @

  line 10 15 5 7ul @
  line 11 12 6 7ul @
  line 8 13 7 7ul @
  line 9 14 4 7ul 

let double_round : shuffle =
  column_round @ diagonal_round

let rounds : shuffle = 
    iter 10 double_round (* 20 rounds *)

let chacha20_core (s:state) : Tot state = 
    let s' = rounds s in
    Combinators.seq_map2 op_Plus_Percent_Hat s' s

(* state initialization *) 

unfold let constants : (s:seq U32.t{length s = 4}) = 
       let l = [0x61707865ul; 0x3320646eul; 0x79622d32ul; 0x6b206574ul] in
         assert_norm(List.Tot.length l = 4);
	 createL l	 

let setup (k:key) (n:nonce) (c:counter): Tot state =
  let constants:seq vec = Combinators.seq_map to_vec constants in
  let key = Combinators.seq_map to_vec (uint32s_from_le 8 k) in
  let nonce = Combinators.seq_map to_vec (uint32s_from_le 3 n) in
  let ctr = create 1 initial_counter in
  constants @| key @| ctr @| nonce

let transpose (s:state): Tot stateT =
    let cols = createL [0;1;2;3;4;5;6;7] in
    Combinators.seq_map (fun i -> Combinators.seq_map (fun r -> index r i) s) cols

let state_to_key (s:state): Tot vec_block =
    let k = transpose s in
    uint32s_to_le 16 (index k 0) @|
    uint32s_to_le 16 (index k 1) @|
    uint32s_to_le 16 (index k 2) @|
    uint32s_to_le 16 (index k 3) @|
    uint32s_to_le 16 (index k 4) @|
    uint32s_to_le 16 (index k 5) @|
    uint32s_to_le 16 (index k 6) @|
    uint32s_to_le 16 (index k 7) 


let chacha20_block (k:key) (n:nonce) (c:counter): Tot vec_block =
    let st = setup k n c in
    let st' = chacha20_core st in
    state_to_key st'    

let chacha20_ctx: Spec.CTR.block_cipher_ctx = 
    let open Spec.CTR in
    {
    keylen = keylen;
    blocklen = 8 * blocklen;
    noncelen = noncelen;
    counterbits = 32;
    incr = 8
    }

let chacha20_cipher: Spec.CTR.block_cipher chacha20_ctx = chacha20_block

let chacha20_encrypt_bytes key nonce counter m = 
    Spec.CTR.counter_mode chacha20_ctx chacha20_cipher key nonce counter m


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
