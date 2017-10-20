module Spec.Chacha20
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Stateful

(* Chacha20 State *)

noeq type state = {
  state_i:lseq uint32 16;
  state  :lseq uint32 16;
}

(* The following types and functions could be 
   automatically generated from the "state" definition above. *)

type key =  | St_i | St

unfold 
let value (k:key) : Type0 = 
  match k with
  | St_i -> uint32
  | St   -> uint32
  
unfold
let length (k:key) : size_t = 
  match k with
  | St_i -> 16
  | St   -> 16

let create_state () = 
  let s = create 16 (u32 0) in
  let s' = create 16 (u32 0) in
  {state_i = s; state = s'}
  
unfold
let get (s:state) (k:key) : lseq (value k) (length k) =
  match k with
  | St_i  -> s.state_i
  | St    -> s.state
  
unfold
let put(s:state) (k:key) (v:lseq (value k) (length k)) : state =
  match k with
  | St_i -> {s with state_i = v}
  | St   -> {s with state = v}

  
(* Stateful monad for Chacha20 *)
let chacha_state_def = StateDef state key value length create_state get put
type chacha_st (a:Type0)  = stateful chacha_state_def a
type index (k:chacha_state_def.key) = st_index chacha_state_def k

(* Chacha20 Spec *)

let line (a:index St) (b:index St) (d:index St) (s:rotval U32) : chacha_st unit =
  mb <-- read St b ;
  ma <-- read St a ;
  write St a ((+.) #U32 ma mb) ;;
  ma <-- read St a ;
  md <-- read St d ;
  write St d ((md ^. ma) <<<. s)

let quarter_round a b c d : chacha_st unit =
  line a b d (u32 16) ;;
  line c d b (u32 12) ;;
  line a b d (u32 8)  ;;
  line c d b (u32 7)

let column_round : chacha_st unit = 
  quarter_round 0 4 8  12 ;;
  quarter_round 1 5 9  13 ;;
  quarter_round 2 6 10 14 ;;
  quarter_round 3 7 11 15

let diagonal_round : chacha_st unit =
  quarter_round 0 5 10 15 ;;
  quarter_round 1 6 11 12 ;;
  quarter_round 2 7 8  13 ;;
  quarter_round 3 4 9  14

let double_round: chacha_st unit =
    column_round ;; 
    diagonal_round (* 2 rounds *)

let rounds : chacha_st unit =
    repeat_st 10 double_round (* 20 rounds *)
 
let chacha20_core: chacha_st unit = 
    copy St_i St ;;
    rounds ;;
    in_place_map2 St_i St ((+.) #U32) 

(* state initialization *)
let c0 = u32 0x61707865
let c1 = u32 0x3320646e
let c2 = u32 0x79622d32
let c3 = u32 0x6b206574

let keylen = 32   (* in bytes *)
let blocklen = 64 (* in bytes *)
let noncelen = 12 (* in bytes *)

type chacha_key   = lbytes keylen
type chacha_block = lbytes blocklen
type chacha_nonce = lbytes noncelen
type counter = size_t


let setup (k:chacha_key) (n:chacha_nonce) (c:counter): chacha_st unit =
  write St_i 0 c0 ;;
  write St_i 1 c1 ;;
  write St_i 2 c2 ;;
  write St_i 3 c3 ;;
  import_slice k (Slice St_i 4 12) (uints_from_bytes_le #U32 #8) ;;
  write St_i 12 (u32 c) ;;
  import_slice n (Slice St_i 13 16) (uints_from_bytes_le #U32 #3) 


let chacha20_block (k:chacha_key) (n:chacha_nonce) (c:counter): Tot chacha_block =
    alloc (
       setup k n c ;;
       chacha20_core ;;
       export St (uints_to_bytes_le #U32 #16)
    )

let chacha20_ctx: Spec.CTR.block_cipher_ctx =
    let open Spec.CTR in
    {
    keylen = keylen;
    noncelen = noncelen;
    countermax = maxint U32;
    blocklen = blocklen;
    }

let chacha20_block_cipher: Spec.CTR.block_cipher chacha20_ctx = chacha20_block

let chacha20_encrypt_bytes key nonce counter len m =
    let chacha20_ctr = Spec.CTR.counter_mode chacha20_ctx chacha20_block_cipher in
    chacha20_ctr key nonce counter len m


let test_plaintext = List.Tot.map u8_uy [
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

let test_ciphertext = List.Tot.map u8_uy [
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

let test_key = List.Tot.map u8_uy [
    0uy;   1uy;  2uy;  3uy;  4uy;  5uy;  6uy;  7uy;
    8uy;   9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy;
    16uy; 17uy; 18uy; 19uy; 20uy; 21uy; 22uy; 23uy;
    24uy; 25uy; 26uy; 27uy; 28uy; 29uy; 30uy; 31uy
    ]

let test_nonce = List.Tot.map u8_uy [
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0x4auy; 0uy; 0uy; 0uy; 0uy
    ]

let test_counter = 1

let test() =
  assert_norm(List.Tot.length test_plaintext = 114);
  assert_norm(List.Tot.length test_ciphertext = 114);
  assert_norm(List.Tot.length test_key = 32);
  assert_norm(List.Tot.length test_nonce = 12);
  let test_plaintext : lbytes 114 = createL test_plaintext in
  let test_ciphertext : lbytes 114 = createL test_ciphertext in
  let test_key : chacha_key = createL test_key in
  let test_nonce :chacha_nonce = createL test_nonce in
  let cipher : lbytes 114 = chacha20_encrypt_bytes test_key test_nonce test_counter 114 test_plaintext in
  for_all2 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) cipher test_ciphertext



