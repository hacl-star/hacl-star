module Spec.CTR

open FStar.Seq
open Spec.Lib

type block_cipher_ctx = {
     keylen: nat ;
     blocklen: (x:nat{x>0});
     noncelen: nat;
     counterbits: nat}

type key (c:block_cipher_ctx) = lbytes c.keylen
type nonce (c:block_cipher_ctx) = lbytes c.noncelen
type block (c:block_cipher_ctx) = lbytes c.blocklen
type counter (c:block_cipher_ctx) = UInt.uint_t c.counterbits
type block_cipher (c:block_cipher_ctx) =  key c -> nonce c -> counter c -> block c

val xor: #len:nat -> x:lbytes len -> y:lbytes len -> Tot (lbytes len)
let xor #len x y = map2 (fun x y -> FStar.UInt8.(x ^^ y)) x y

val counter_mode: 
  ctx: block_cipher_ctx ->
  bc: block_cipher ctx ->
  k:key ctx -> n:nonce ctx -> c:counter ctx -> 
  plain:seq UInt8.t{c + (length plain / ctx.blocklen) < pow2 ctx.counterbits} ->
  Tot (lbytes (length plain))
  (decreases (length plain))
#reset-options "--z3rlimit 40 --max_fuel 2"
let rec counter_mode ctx block_enc key nonce counter plain =
  let len = length plain in 
  if len = 0 then Seq.createEmpty #UInt8.t else
  if len <= ctx.blocklen 
  then (* encrypt final partial block *)
      let mask = block_enc key nonce counter in 
      let mask = slice mask 0 len in 
      xor plain mask
  else (* encrypt full block *)
      let (b, plain) = split plain ctx.blocklen in 
      let mask = block_enc key nonce counter in 
      let eb = xor b mask in
      let cipher = counter_mode ctx block_enc key nonce (counter + 1) plain in
      eb @| cipher 

