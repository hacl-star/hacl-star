module Spec.CTR

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

noeq
type cipher =
  | Cipher: state:Type ->
	    key_len:size_nat ->
	    nonce_len:size_nat ->
	    counter_max:size_nat ->
	    block_len:(x:size_nat{x>0}) ->
	    init:(lbytes key_len -> lbytes nonce_len -> state) ->
	    set_counter:(state -> c:size_nat{c <= counter_max} -> state) ->
	    key_block: (state -> lbytes block_len) ->
	    cipher


val xor: #len:size_nat -> x:lbytes len -> y:lbytes len -> Tot (lbytes len)
let xor #len x y = map2 (fun x y -> x ^. y) x y

val counter_mode_blocks:
  enc: cipher ->
  st0:enc.state ->
  c:size_nat ->
  n:size_nat{n * enc.block_len < pow2 32 /\ c + n <= enc.counter_max} ->
  plain:lbytes (n * enc.block_len) ->
  Tot (lbytes (n * enc.block_len))
#set-options "--z3rlimit 1000"
let counter_mode_blocks enc st0 counter n plain =
  let ciphertext = create (n * enc.block_len) (u8 0) in
  repeati n
    (fun i cipher ->
      let st = enc.set_counter st0 (counter + i) in
      let b = slice plain (i * enc.block_len) ((i+1) * enc.block_len) in
      let k = enc.key_block st in
      let c = xor b k in
      update_slice cipher (i * enc.block_len) ((i+1) * enc.block_len) c)
      ciphertext

val counter_mode:
  enc: cipher ->
  k:lbytes enc.key_len ->
  n:lbytes enc.nonce_len ->
  c:size_nat{c <= enc.counter_max} ->
  len: size_nat{c + (len / enc.block_len) <= enc.counter_max}  ->
  plain:lbytes len  ->
  Tot (lbytes len)
let counter_mode enc key nonce counter len plain =
  let n      = len / enc.block_len in
  let rem    = len % enc.block_len in
  let st0 = enc.init key nonce in
  let blocks = slice plain 0 (n * enc.block_len) in
  let cipher_blocks = counter_mode_blocks enc st0 counter n blocks in
  if rem = 0 then cipher_blocks
  else
      let st = enc.set_counter st0 (counter + n) in
      let k = enc.key_block st in
      let k' = slice k 0 rem in
      let last : lbytes rem = slice plain (n * enc.block_len) len in
      let cipher_last: lbytes rem = xor #rem last k' in
      let cipher = create len (u8 0) in
      let cipher = update_slice cipher 0 (n * enc.block_len) cipher_blocks in
      update_slice cipher (n * enc.block_len) len cipher_last
