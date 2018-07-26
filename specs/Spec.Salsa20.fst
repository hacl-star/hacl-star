module Spec.Salsa20

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes


#set-options "--max_fuel 0 --z3rlimit 100"

(* Constants *)
let size_key = 32 (* in bytes *)
let size_block = 64  (* in bytes *)
let size_nonce = 8   (* in bytes *)

type key = lbytes size_key
type block = lbytes size_block
type nonce = lbytes size_nonce
type counter = size_nat

type state = m:intseq U32 16
type idx = n:size_nat{n < 16}
type shuffle = state -> Tot state

// Using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x)


let line (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:state) =
  let m = m.[a] <- (m.[a] ^. ((m.[b] +. m.[d]) <<<. s)) in
  m

let quarter_round a b c d : shuffle =
  line b a d (u32 7) @
  line c b a (u32 9) @
  line d c b (u32 13) @
  line a d c (u32 18)

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

let salsa20_core (s:state) : Tot state =
  let s' = rounds s in
  map2 (fun x y -> x +. y) s' s

(* state initialization *)
let constant0 = 0x61707865
let constant1 = 0x3320646e
let constant2 = 0x79622d32
let constant3 = 0x6b206574


let setup (k:key) (n:nonce) (st:state) : Tot state =
  let ks = uints_from_bytes_le #U32 #8 k in
  let ns = uints_from_bytes_le #U32 #2 n in
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

let salsa20_cipher =
  Spec.CTR.Cipher state size_key max_size_t size_block salsa20_init salsa20_set_counter salsa20_key_block

let salsa20_encrypt_bytes key nonce counter m =
  Spec.CTR.counter_mode salsa20_cipher key nonce counter m
