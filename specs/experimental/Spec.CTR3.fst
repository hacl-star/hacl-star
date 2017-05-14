module Spec.CTR3

open FStar.Mul
open FStar.Seq
open Spec.Lib

open Spec.CTR


#reset-options "--max_fuel 0"

val counter_mode_blocks3:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{192 * len = length plain /\ c + 192 * len < pow2 32} ->
  Tot (lbytes (length plain))
      (decreases (len))
#reset-options "--z3rlimit 20 --max_fuel 0"
let rec counter_mode_blocks3 key nonce counter plain len =
  if len = 0 then Seq.createEmpty #UInt8.t
  else (
    assert(length plain >= 192);
    let prefix, block = split plain (length plain - 192) in    
    let cipher = counter_mode_blocks3 key nonce counter prefix (len - 1) in
    let mask0  = Spec.Chacha20_vec.chacha20_block key nonce (counter + (len - 1)) in
    let mask1  = Spec.Chacha20_vec.chacha20_block key nonce (counter + (len    )) in
    let mask2  = Spec.Chacha20_vec.chacha20_block key nonce (counter + (len + 1)) in
    let mask   = mask0 @| mask1 @| mask2 in
    assert(length mask = 192);
    assert(length block = 192);
    assert(length cipher = length plain - 192);
    let eb     = xor #192 block mask in
    cipher @| eb
  )


val counter_mode:
  k:key Spec.Chacha20_vec.chacha20_ctx ->
  n:nonce Spec.Chacha20_vec.chacha20_ctx ->
  c:counter Spec.Chacha20_vec.chacha20_ctx ->
  plain:seq UInt8.t ->
  len:nat{64 * len = length plain /\ c + 64 * len < pow2 32} ->
  Tot (lbytes (length plain))
#reset-options "--z3rlimit 20 --max_fuel 0"
let counter_mode key nonce counter plain len =
  (* let len = length plain in *)
  let blocks_len = (ctx.incr * ctx.blocklen) * (len / (ctx.blocklen * ctx.incr)) in
  let part_len   = len % (ctx.blocklen * ctx.incr) in
    (* TODO: move to a single lemma for clarify *)
    Math.Lemmas.lemma_div_mod len (ctx.blocklen * ctx.incr);
    Math.Lemmas.multiple_modulo_lemma (len / (ctx.blocklen * ctx.incr)) (ctx.blocklen * ctx.incr);
    Math.Lemmas.lemma_div_le (blocks_len) len ctx.blocklen;
    (* End TODO *)
  let blocks, last_block = split plain blocks_len in
  let cipher_blocks = counter_mode_blocks ctx block_enc key nonce counter blocks in
  let cipher_last_block =
    if part_len > 0
    then (* encrypt final partial block(s) *)
      let mask = block_enc key nonce (counter+ctx.incr*(length plain / ctx.blocklen)) in
      let mask = slice mask 0 part_len in
      assert(length last_block = part_len);
      xor #part_len last_block mask
    else createEmpty in
  cipher_blocks @| cipher_last_block
