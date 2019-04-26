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
  Tot block
let xor_block out in1 in2  =
  Lib.LoopCombinators.repeati blocklen (fun i out ->
     out.[i] <- in1.[i] ^. in2.[i]
  ) out

#set-options "--z3rlimit 100"

val cbc_encrypt_blocks:
  out:seq uint8{length out % blocklen == 0} ->
  kex:xkey ->
  iv:block ->
  msg:seq uint8{length out == length msg} ->
  len:size_nat{length msg == len}  ->
  Tot (out':seq uint8{length out' == length out})
let rec cbc_encrypt_blocks out kex iv msg len =
  let (_, new_out) = Lib.LoopCombinators.repeati (len / blocklen) (fun b (prev, out) ->
    let mblock = sub #uint8 #(length msg) msg (b * blocklen) blocklen in
    let tmp = create blocklen (u8 0) in
    let tmp = xor_block tmp mblock prev in
    let oblock = cipher tmp kex in
    let out' = update_sub #uint8 #(len) out (b * blocklen) blocklen oblock in
    (oblock, out')
  ) (iv, out)
  in new_out

#set-options "--z3rlimit 10"

val padPKCS:
  tmp:block ->
  len:size_nat{len <= blocklen} ->
  idx:size_nat{idx <= blocklen} ->
  Tot block
let padPKCS tmp len idx =
  Lib.LoopCombinators.repeati (blocklen - idx) (fun i tmp ->
    let i = idx + i in
    upd #uint8 #blocklen tmp i (u8 len)
  ) tmp

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

#set-options "--z3rlimit 100"

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
  let out1 = cbc_encrypt_blocks out1 kex iv msg1 fullblocks in
  let lastfull  = if fullblocks <> 0 then
    sub #uint8 #(fullblocks) out1 (fullblocks - blocklen) blocklen
  else
    iv
  in
  let ltmp = create blocklen (u8 0) in
  let ltmp = update_sub ltmp 0 final last in
  let ltmp = pad ltmp (blocklen - final) final in
  let ltmp = xor_block ltmp ltmp lastfull in
  let otmp = cipher ltmp kex in
  concat_with_last_block fullblocks out1 otmp

#set-options "--z3rlimit 40"

val cbc_decrypt_blocks:
  out:seq uint8{length out % blocklen == 0} ->
  kex:xkey ->
  iv:block ->
  cip:seq uint8{length out == length cip} ->
  len:size_nat{len == length cip} ->
  Tot (out':seq uint8{length out' == length out})
let cbc_decrypt_blocks out kex iv cip len =
  let (_, new_out) = Lib.LoopCombinators.repeati (len / blocklen) (fun b (prev, out) ->
    let cblock = sub #uint8 #(length cip) cip (b * blocklen) blocklen in
    let tmp = inv_cipher cblock kex in
    let oblock = xor_block tmp tmp prev in
    let out' = update_sub #uint8 #(len) out (b * blocklen) blocklen oblock in
    (cblock, out')
  ) (iv, out) in
  new_out

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
  let out = cbc_decrypt_blocks out kex iv cip ciplen in
  let pad : uint8 = index #uint8 #ciplen out (ciplen - 1) in
  let pad = uint_to_nat pad in
  if pad > 0 && pad <= blocklen then begin
    Some(sub #uint8 #ciplen out 0 (ciplen - pad))
  end else None
