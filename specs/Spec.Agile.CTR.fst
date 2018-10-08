module Spec.Agile.CTR

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.Agile.Cipher

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

val xor: #len:size_nat -> x:lbytes len -> y:lbytes len -> Tot (lbytes len)
let xor #len x y = map2 (fun x y -> logxor #U8 x y) x y

val process_block:
  a:cipher_alg ->
  st0:state a ->
  c:size_nat {c <= counter_max a} ->
  plain:lbytes (block_len a) ->
  Tot (lbytes (block_len a))
let process_block a st0 c plain =
  let st = set_counter a st0 c in
  let k = key_block a st in
  let c = xor plain k in
  c

val counter_mode_blocks:
  a:cipher_alg ->
  st0:state a ->
  c:size_nat ->
  n:size_nat{n * block_len a < pow2 32 /\ c + n <= counter_max a} ->
  plain:lbytes (n * block_len a) ->
  Tot (lbytes (n * block_len a))
let counter_mode_blocks a st0 counter n plain =
  let ciphertext = create (n * block_len a) (u8 0) in
  repeati n
    (fun i cipher ->
      let start : size_nat = i * block_len a in
      let b = sub plain start (block_len a) in
      let c = process_block a st0 (counter + i) b in
      update_sub cipher start (block_len a) c)
    ciphertext

val counter_mode:
  a:cipher_alg ->
  k:lbytes (key_len a) ->
  n_len:(nonce_len a) ->
  n:lbytes n_len ->
  c:size_nat{c <= counter_max a} ->
  len: size_nat{c + (len / block_len a) <= counter_max a}  ->
  plain:lbytes len  ->
  Tot (lbytes len)
let counter_mode a key n_len nonce counter len plain =
  let n      = len / block_len a in
  let rem    = len % block_len a in
  let st0 = init a key n_len nonce in
  let blocks = sub plain 0 (n * block_len a) in
  let cipher_blocks = counter_mode_blocks a st0 counter n blocks in
  if rem = 0 then cipher_blocks
  else
      let st = set_counter a st0 (counter + n) in
      let k = key_block a st in
      let k' = slice k 0 rem in
      let last : lbytes rem = slice plain (n * block_len a) len in
      let cipher_last: lbytes rem = xor #rem last k' in
      let cipher = create len (u8 0) in
      let cipher = update_slice cipher 0 (n * block_len a) cipher_blocks in
      update_slice cipher (n * block_len a) len cipher_last
