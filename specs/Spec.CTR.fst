module Spec.CTR

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

type block_cipher_ctx = {
  keylen: size_t ;
  blocklen: (x:size_t{x>0});
  noncelen: size_t;
  countermax: size_t
}

type key (c:block_cipher_ctx) = lbytes c.keylen
type nonce (c:block_cipher_ctx) = lbytes c.noncelen
type block (c:block_cipher_ctx) = lbytes c.blocklen
type counter (c:block_cipher_ctx) = s:size_t{s <= c.countermax}

type block_cipher (c:block_cipher_ctx) =  key c -> nonce c -> counter c -> block c

val xor: #len:size_t -> x:lbytes len -> y:lbytes len -> Tot (lbytes len)
let xor #len x y = map2 (fun x y -> x ^. y) x y

val counter_mode_blocks:
  ctx: block_cipher_ctx ->
  bc: block_cipher ctx ->
  k:key ctx -> n:nonce ctx -> c:counter ctx ->
  n:size_t{n * ctx.blocklen < pow2 32 /\ c + n <= ctx.countermax} ->
  plain:lbytes (n * ctx.blocklen) ->
  Tot (lbytes (n * ctx.blocklen))
let counter_mode_blocks ctx block_enc key nonce counter n plain =
  let cipher = create (n * ctx.blocklen) (u8 0) in
  repeati n
    (fun i cipher ->
      let b = slice plain (ctx.blocklen * i) (ctx.blocklen * (i+1)) in
      let k = block_enc key nonce (counter + i) in
      let c = xor b k in
      update_slice cipher (ctx.blocklen * i) (ctx.blocklen * (i+1)) c) cipher


val counter_mode:
  ctx: block_cipher_ctx ->
  bc: block_cipher ctx ->
  k:key ctx -> n:nonce ctx -> c:counter ctx ->
  len: size_t{c + (len / ctx.blocklen) <= ctx.countermax}  ->
  plain:lbytes len ->
  Tot (lbytes len)
let counter_mode ctx block_enc key nonce counter len plain =
  let n      = len / ctx.blocklen in
  let rem    = len % ctx.blocklen in
  let blocks = slice plain 0 (n * ctx.blocklen) in
  let cipher_blocks = counter_mode_blocks ctx block_enc key nonce counter n blocks in
  if rem = 0 then cipher_blocks
  else
      let k = block_enc key nonce (counter+n) in
      let k' = slice k 0 rem in
      let last : lbytes rem = slice plain (n * ctx.blocklen) len in
      let cipher_last: lbytes rem = xor #rem last k' in
      let cipher = create len (u8 0) in
      let cipher = update_slice cipher 0 (n * ctx.blocklen) cipher_blocks in
      update_slice cipher (n * ctx.blocklen) len cipher_last
