module Spec.Salsa20

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open Lib.LoopCombinators

#set-options "--max_fuel 0 --z3rlimit 100"

(* Constants *)
let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 8   (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type nonce = lbytes noncelen
type counter = size_nat

type state = m:lseq uint32 16
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
  repeati 10 (fun i -> double_round) (* 20 rounds *)

let salsa20_core (s:state) : Tot state =
  let s' = rounds s in
  map2 (fun x y -> x +. y) s' s

(* state initialization *)
let constant0 = 0x61707865
let constant1 = 0x3320646e
let constant2 = 0x79622d32
let constant3 = 0x6b206574


let setup (k:key) (n:nonce) (st:state) : Tot state =
  let ks = uints_from_bytes_le #U32 #SEC #8 k in
  let ns = uints_from_bytes_le #U32 #SEC #2 n in
  let st = st.[0] <- u32 constant0 in
  let st = update_sub st 1 4 (slice ks 0 4) in
  let st = st.[5] <- u32 constant1 in
  let st = update_sub st 6 2 (slice ns 0 2) in
  let st = st.[10] <- u32 constant2 in
  let st = update_sub st 11 4 (slice ks 4 8) in
  let st = st.[15] <- u32 constant3 in
  st

let salsa20_init (k:key) (n_len:size_nat) (n:nonce) : Tot state =
  let st = create 16 (u32 0) in
  let st  = setup k n st in
  st

let salsa20_set_counter (st:state) (c:counter) : Tot state =
  let st = st.[8] <- (u32 c) in
  st.[9] <- (u32 0)

let salsa20_key_block (st:state) : Tot block =
  let st' = salsa20_core st in
  uints_to_bytes_le st'

let salsa20_encrypt_block (st0:state) (ctr0:counter) (incr:counter{ctr0 + incr <= max_size_t}) (b:block) : Tot block =
  let st = salsa20_set_counter st0 (ctr0 + incr) in
  let kb = salsa20_key_block st in
  map2 (^.) b kb

let salsa20_encrypt_last (st0:state) (ctr0:counter) 
			  (incr:counter{ctr0 + incr <= max_size_t}) 
			  (len:size_nat{len < blocklen})
			  (b:lbytes len) : lbytes len =
  let plain = create blocklen (u8 0) in
  let plain = update_sub plain 0 (length b) b in
  let cipher = salsa20_encrypt_block st0 ctr0 incr plain in
  sub cipher 0 (length b)

val salsa20_encrypt_bytes:
  key -> nonce -> c:counter 
-> msg:bytes{length msg / blocklen + c <= max_size_t} 
-> cipher:bytes{length cipher == length msg}

let salsa20_encrypt_bytes key nonce ctr0 msg =
  let cipher = msg in
  let st0 = salsa20_init key 8 nonce in
  map_blocks blocklen cipher
    (salsa20_encrypt_block st0 ctr0) 
    (salsa20_encrypt_last st0 ctr0)
