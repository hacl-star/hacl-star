module Spec.Salsa20

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open Lib.LoopCombinators

#set-options "--max_fuel 0 --z3rlimit 100"

(* Constants *)
let size_key = 32 (* in bytes *)
let size_block = 64  (* in bytes *)
let size_nonce = 8   (* in bytes *)
let size_xnonce = 16   (* in bytes *)

type key = lbytes size_key
type block = lbytes size_block
type nonce = lbytes size_nonce
type xnonce = lbytes size_xnonce
type counter = size_nat

type state = lseq uint32 16
type idx = n:size_nat{n < 16}
type shuffle = state -> Tot state

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)


let line (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:state) : state =
  let m = m.[a] <- (m.[a] ^. ((m.[b] +. m.[d]) <<<. s)) in
  m

let quarter_round a b c d : shuffle =
  line b a d (size 7) @
  line c b a (size 9) @
  line d c b (size 13) @
  line a d c (size 18)

let column_round : shuffle =
  quarter_round 0 4 8 12 @
  quarter_round 5 9 13 1 @
  quarter_round 10 14 2 6 @
  quarter_round 15 3 7 11

let row_round : shuffle =
  quarter_round 0 1 2 3  @
  quarter_round 5 6 7 4 @
  quarter_round 10 11 8 9 @
  quarter_round 15 12 13 14

let double_round: shuffle =
  column_round @ row_round (* 2 rounds *)

let rounds : shuffle =
  repeat 10 double_round (* 20 rounds *)

let salsa20_add_counter (s:state) (ctr:counter) : Tot state =
  s.[8] <- s.[8] +. (u32 ctr)

let salsa20_core (ctr:counter) (s:state) : Tot state =
  let s' = salsa20_add_counter s ctr in
  let s' = rounds s' in
  let s' = map2 (+.) s' s in
  salsa20_add_counter s' ctr

(* state initialization *)
inline_for_extraction
let constant0 = u32 0x61707865
inline_for_extraction
let constant1 = u32 0x3320646e
inline_for_extraction
let constant2 = u32 0x79622d32
inline_for_extraction
let constant3 = u32 0x6b206574


let setup (k:key) (n:nonce) (ctr0:counter) (st:state) : Tot state =
  let ks = uints_from_bytes_le #U32 #SEC #8 k in
  let ns = uints_from_bytes_le #U32 #SEC #2 n in
  let st = st.[0] <- constant0 in
  let st = update_sub st 1 4 (slice ks 0 4) in
  let st = st.[5] <- constant1 in
  let st = update_sub st 6 2 ns in
  let st = st.[8] <- u32 ctr0 in
  let st = st.[9] <- u32 0 in
  let st = st.[10] <- constant2 in
  let st = update_sub st 11 4 (slice ks 4 8) in
  let st = st.[15] <- constant3 in
  st

let salsa20_init (k:key) (n:nonce) (ctr0:counter) : Tot state =
  let st = create 16 (u32 0) in
  let st  = setup k n ctr0 st in
  st

let xsetup (k:key) (n:xnonce) (st:state) : Tot state =
  let ks = uints_from_bytes_le #U32 #SEC #8 k in
  let ns = uints_from_bytes_le #U32 #SEC #4 n in
  let st = st.[0] <- constant0 in
  let st = update_sub st 1 4 (slice ks 0 4) in
  let st = st.[5] <- constant1 in
  let st = update_sub st 6 4 ns in
  let st = st.[10] <- constant2 in
  let st = update_sub st 11 4 (slice ks 4 8) in
  let st = st.[15] <- constant3 in
  st

let hsalsa20_init (k:key) (n:xnonce) : Tot state =
  let st = create 16 (u32 0) in
  let st  = xsetup k n st in
  st

let hsalsa20 (k:key) (n:xnonce) : Tot (lbytes 32) =
  let st = hsalsa20_init k n in
  let st = rounds st in
  [@inline_let]
  let res_l = [st.[0]; st.[5]; st.[10]; st.[15]; st.[6]; st.[7]; st.[8]; st.[9]] in
  assert_norm(List.Tot.length res_l == 8);
  let res = createL res_l in
  uints_to_bytes_le res

let salsa20_key_block (st:state) : Tot block =
  let st' = salsa20_core 0 st in
  uints_to_bytes_le st'

let salsa20_key_block0 (k:key) (n:nonce) : Tot block =
  let st = salsa20_init k n 0 in
  salsa20_key_block st

let xor_block (k:state) (b:block) : block  =
  let ib = uints_from_bytes_le b in
  let ob = map2 (^.) ib k in
  uints_to_bytes_le ob

let salsa20_encrypt_block (st0:state) (incr:counter) (b:block) : Tot block =
  let k = salsa20_core incr st0 in
  xor_block k b

let salsa20_encrypt_last (st0:state) (incr:counter)
			  (len:size_nat{len < size_block})
			  (b:lbytes len) : lbytes len =
  let plain = create size_block (u8 0) in
  let plain = update_sub plain 0 (length b) b in
  let cipher = salsa20_encrypt_block st0 incr plain in
  sub cipher 0 len

val salsa20_update:
    ctx: state
  -> msg: bytes{length msg / size_block <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let salsa20_update ctx msg =
  let cipher = msg in
  map_blocks size_block cipher
    (salsa20_encrypt_block ctx)
    (salsa20_encrypt_last ctx)


val salsa20_encrypt_bytes:
    k: key
  -> n: nonce
  -> c: counter
  -> msg: bytes{length msg / size_block <= max_size_t}
  -> cipher: bytes{length cipher == length msg}

let salsa20_encrypt_bytes key nonce ctr0 msg =
  let st0 = salsa20_init key nonce ctr0 in
  salsa20_update st0 msg


val salsa20_decrypt_bytes:
    k: key
  -> n: nonce
  -> c: counter
  -> cipher: bytes{length cipher / size_block <= max_size_t}
  -> msg: bytes{length cipher == length msg}

let salsa20_decrypt_bytes key nonce ctr0 cipher =
  let st0 = salsa20_init key nonce ctr0 in
  salsa20_update st0 cipher
