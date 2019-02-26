module Spec.AES256_CBC

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Spec.AES256

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 10"

val xor_block:
  out:block ->
  in1:block ->
  in2:block ->
  start:size_nat{start <=  blocklen} ->
  Tot block (decreases (blocklen - start))
let rec xor_block out in1 in2 start =
    if start = blocklen then out
    else
      let out = out.[start] <- in1.[start] ^. in2.[start] in
      xor_block out in1 in2 (start + 1)

#set-options "--z3rlimit 100"

val cbc_encrypt_blocks:
  out:seq uint8{length out % blocklen == 0} ->
  kex:xkey ->
  prev:block ->
  msg:seq uint8{length out == length msg} ->
  len:size_nat{length msg == len}  ->
  curr:size_nat{curr <= len /\ curr % blocklen == 0} ->
  Tot (out':seq uint8{length out' == length out}) (decreases (len - curr))
let rec cbc_encrypt_blocks out kex prev msg len curr =
  if curr = len then out
  else begin
    let mblock = sub #uint8 #(length msg) msg curr blocklen in
    let tmp = create blocklen (u8 0) in
    let tmp = xor_block tmp mblock prev 0 in
    let oblock = cipher tmp kex in
    let out' = update_sub #uint8 #(len) out curr blocklen oblock in
    cbc_encrypt_blocks out' kex oblock msg len (curr + blocklen)
  end

#set-options "--z3rlimit 10"

val padPKCS:
  tmp:block ->
  len:size_nat{len <= blocklen} ->
  idx:size_nat{idx <= blocklen} ->
  Tot block (decreases (blocklen - idx))
let rec padPKCS tmp len idx =
    if idx = blocklen then tmp
    else
      let tmp = tmp.[idx] <-  u8 len in
      padPKCS tmp len (idx + 1)

let pad tmp len idx = padPKCS tmp len idx

val concat_with_last_block:
  first_part_length:size_nat{
    first_part_length % blocklen == 0 /\ first_part_length + blocklen <= max_size_t
  } ->
  first_part:lseq uint8 first_part_length ->
  last_block:block ->
  Tot (out:seq uint8{length out = first_part_length + blocklen})
let concat_with_last_block first_part_length first_part last_block =
  if first_part_length < blocklen then begin
    let out = create blocklen (u8 0) in
    update_sub out 0 blocklen last_block
  end else begin
    let lastfull_offset : size_nat = first_part_length in
    let out = create (first_part_length + blocklen) (u8 0) in
    let out = update_sub out
      0 lastfull_offset
      (sub first_part 0 lastfull_offset)
    in
    update_sub out lastfull_offset blocklen last_block
  end

#set-options "--z3rlimit 70"

let cipherlen plen = ((plen + blocklen) / blocklen) `op_Multiply` blocklen

val aes256_cbc_encrypt:
  key:skey ->
  iv:block ->
  msg:seq uint8{length msg + blocklen <= max_size_t} ->
  msglen:size_nat{msglen == length msg} ->
  Tot (out:seq uint8{length out == cipherlen msglen})
let aes256_cbc_encrypt key iv msg msglen =
  let fullblocks = (msglen / blocklen) * blocklen in
  let final = msglen % blocklen in
  let msg1 = sub #uint8 #(length msg) msg 0 fullblocks in
  let last = sub #uint8 #(length msg) msg fullblocks final in
  let out1 = create fullblocks (u8 0) in
  let kex = keyExpansion key in
  let out1 = cbc_encrypt_blocks out1 kex iv msg1 fullblocks 0 in
  let lastfull  = if fullblocks <> 0 then
    sub #uint8 #(fullblocks) out1 (fullblocks - blocklen) blocklen
  else
    iv
  in
  let ltmp = create blocklen (u8 0) in
  let ltmp = update_sub ltmp 0 final last in
  let ltmp = pad ltmp (blocklen - final) final in
  let ltmp = xor_block ltmp ltmp lastfull 0 in
  let otmp = cipher ltmp kex in
  concat_with_last_block fullblocks out1 otmp

#set-options "--z3rlimit 40"

val cbc_decrypt_blocks:
  out:seq uint8{length out % blocklen == 0} ->
  kex:xkey ->
  prev:block ->
  cip:seq uint8{length out == length cip} ->
  len:size_nat{len == length cip} ->
  curr:size_nat{curr % blocklen == 0 /\ curr <= len} ->
  Tot (out':seq uint8{length out' == length out}) (decreases (len - curr))
let rec cbc_decrypt_blocks out kex prev cip len curr =
  if curr = len then out
  else
    let cblock = sub #uint8 #(length cip) cip curr blocklen in
    let tmp = inv_cipher cblock kex in
    let oblock = xor_block tmp tmp prev 0 in
    let out' = update_sub #uint8 #(len) out curr blocklen oblock in
    cbc_decrypt_blocks out' kex cblock cip len (curr + blocklen)

val aes256_cbc_decrypt:
  key: skey ->
  iv: block ->
  cip: seq uint8{
    length cip % blocklen == 0 /\ length cip > 0 /\
    length cip <= max_size_t
  } ->
  ciplen:size_nat{ciplen == length cip} ->
  Tot (out:option (out':seq uint8{
    length out' + blocklen <= max_size_t /\
    cipherlen (length out') = length cip
  }))
let aes256_cbc_decrypt key iv cip ciplen =
  let kex = keyExpansion key in
  let out : lseq uint8 ciplen = create ciplen (u8 0) in
  let out = cbc_decrypt_blocks out kex iv cip ciplen 0 in
  let pad : uint8 = index #uint8 #ciplen out (ciplen - 1) in
  let pad = uint_to_nat pad in
  if pad > 0 && pad <= blocklen then begin
    Some(sub #uint8 #ciplen out 0 (ciplen - pad))
  end else None
