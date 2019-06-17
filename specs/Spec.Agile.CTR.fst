module Spec.Agile.CTR

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.Agile.Cipher

#reset-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

val process_block:
  a:cipher_alg ->
  st0:state a ->
  c:size_nat {c <= counter_max a} ->
  plain:lbytes (block_len a) ->
  Tot (lbytes (block_len a))
let process_block a st0 c plain =
  let st = add_counter a st0 c in
  let k = key_block a st in
  let c = map2 ( ^. ) plain k in
  c

val process_last:
  a:cipher_alg ->
  st0:state a ->
  c:size_nat {c <= counter_max a} ->
  len:size_nat{len < block_len a} ->
  plain:lbytes len ->
  Tot (lbytes len)
let process_last a st0 c len plain =
 let last = create (block_len a) (u8 0) in
 let last = update_sub last 0 len plain in
 let cipher = process_block a st0 c last in
 sub cipher 0 len

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
  let st0 = init a key n_len nonce counter in
  map_blocks (block_len a) plain
    (process_block a st0)
    (process_last a st0)
