module Spec.Chacha20

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators


#set-options "--max_fuel 0 --z3rlimit 100"

/// Constants and Types

let size_key = 32
let size_block = 64
let size_nonce = 12

(* TODO: Remove, left here to avoid breaking implementation *)
let keylen = 32   (* in bytes *)
let blocklen = 64 (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes size_key
type block = lbytes size_block
type nonce = lbytes size_nonce
type counter = size_nat
type subblock = b:bytes{length b <= size_block}

// Internally, blocks are represented as 16 x 4-byte integers
type state = lseq uint32 16
type idx = n:size_nat{n < 16}
type shuffle = state -> Tot state

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)


/// Specification

let line (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:state) : Tot state =
  let m = m.[a] <- (m.[a] +. m.[b]) in
  let m = m.[d] <- ((m.[d] ^. m.[a]) <<<. s) in m

let quarter_round a b c d : Tot shuffle =
  line a b d (size 16) @
  line c d b (size 12) @
  line a b d (size 8)  @
  line c d b (size 7)

let column_round : shuffle =
  quarter_round 0 4 8  12 @
  quarter_round 1 5 9  13 @
  quarter_round 2 6 10 14 @
  quarter_round 3 7 11 15

let diagonal_round : shuffle =
  quarter_round 0 5 10 15 @
  quarter_round 1 6 11 12 @
  quarter_round 2 7 8  13 @
  quarter_round 3 4 9  14

let double_round : shuffle =
  column_round @ diagonal_round (* 2 rounds *)

let rounds : shuffle =
  repeat 10 double_round (* 20 rounds *)

let sum_state (s0:state) (s1:state) : Tot state =
  map2 (+.) s0 s1

let chacha20_add_counter (s0:state) (ctr:counter) : Tot state =
  s0.[12] <- s0.[12] +. u32 ctr

// protz 10:37 AM
//   question about chacha20 spec: why the double counter increment in chacha20_core?
//   https://github.com/project-everest/hacl-star/blob/_dev/specs/Spec.Chacha20.fst#L75
//   is this in the spec?
// karthik 11:28 AM
//   This is doing the same as:
//
//   let chacha20_core (ctr:counter) (s0:state)  : Tot state =
//     let s0 = chacha20_add_counter s0 ctr in
//     let k = rounds s0 in
//     sum_state k s0
//
//   but we rewrite in this way so that s0 remains constant
//   (in the code)
// protz 11:32 AM
//   do sum_state and add_counter commute?
//   I feel like I'm missing some equational property of these sub-combinators
//   to understand why this is true
// karthik 11:33 AM
//   yes, they do.
let chacha20_core (ctr:counter) (s0:state)  : Tot state =
  let k = chacha20_add_counter s0 ctr in
  let k = rounds k in
  let k = sum_state k s0 in
  chacha20_add_counter k  ctr

inline_for_extraction
let c0 = 0x61707865ul
inline_for_extraction
let c1 = 0x3320646eul
inline_for_extraction
let c2 = 0x79622d32ul
inline_for_extraction
let c3 = 0x6b206574ul

let chacha20_constants : lseq size_t 4 =
  [@ inline_let]
  let l = [c0;c1;c2;c3] in
  assert_norm(List.Tot.length l == 4);
  createL l

let setup (k:key) (n:nonce) (ctr0:counter) (st:state) : Tot state =
  let st = update_sub st 0 4 (map secret chacha20_constants) in
  let st = update_sub st 4 8 (uints_from_bytes_le #U32 #SEC #8 k) in
  let st = st.[12] <- u32 ctr0 in
  let st = update_sub st 13 3 (uints_from_bytes_le #U32 #SEC #3 n) in
  st

let chacha20_init (k:key) (n:nonce) (ctr0:counter) : Tot state =
  let st = create 16 (u32 0) in
  let st  = setup k n ctr0 st in
  st

let chacha20_key_block0 (k:key) (n:nonce) : Tot block =
  let st = chacha20_init k n 0 in
  let st = chacha20_core 0 st in
  uints_to_bytes_le st

let chacha20_key_block (st:state) : Tot block =
  let st = chacha20_core 0 st in
  uints_to_bytes_le st

let xor_block (k:state) (b:block) : block  =
  let ib = uints_from_bytes_le b in
  let ob = map2 (^.) ib k in
  uints_to_bytes_le ob

let chacha20_encrypt_block (st0:state) (incr:counter) (b:block) : Tot block =
  let k = chacha20_core incr st0 in
  xor_block k b

let chacha20_encrypt_last
  (st0: state)
  (incr: counter)
  (len: size_nat{len < size_block})
  (b: lbytes len) :
  Tot (lbytes len) =

  let plain = create size_block (u8 0) in
  let plain = update_sub plain 0 len b in
  let cipher = chacha20_encrypt_block st0 incr plain in
  sub cipher 0 (length b)


val chacha20_update:
    ctx: state
  -> msg: bytes{length msg / size_block <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let chacha20_update ctx msg =
  let cipher = msg in
  map_blocks size_block cipher
    (chacha20_encrypt_block ctx)
    (chacha20_encrypt_last ctx)


val chacha20_encrypt_bytes:
    k: key
  -> n: nonce
  -> c: counter
  -> msg: bytes{length msg / size_block <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let chacha20_encrypt_bytes key nonce ctr0 msg =
  let st0 = chacha20_init key nonce ctr0 in
  chacha20_update st0 msg


val chacha20_decrypt_bytes:
    k: key
  -> n: nonce
  -> c: counter
  -> cipher: bytes{length cipher / size_block <= max_size_t}
  -> msg: bytes{length cipher == length msg}

let chacha20_decrypt_bytes key nonce ctr0 cipher =
  let st0 = chacha20_init key nonce ctr0 in
  chacha20_update st0 cipher
