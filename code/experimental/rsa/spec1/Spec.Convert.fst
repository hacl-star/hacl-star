module Spec.Convert

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.Endian

let bignum_i len = intseq U64 len
let bytes_i len = intseq U8 len

let size_pos = x:size_nat{x > 0}
#reset-options "--z3rlimit 50 --max_fuel 0"
let blocks (x:size_nat) (m:size_nat{m > 0}): (r:size_nat{x <= m * r}) =
  if x < 1 then 0
  else (x - 1) / m + 1

val text_to_nat_:
  len:size_pos -> input:bytes_i len ->
  resLen:size_pos{len = 8 * resLen} -> res:bignum_i resLen -> Tot (res:bignum_i resLen)
let text_to_nat_ len input resLen res =
  repeati resLen
  (fun i res ->
    let res_i = resLen - i - 1 in
    let inputi = uint_from_bytes_be #U64 (sub input (8 * i) 8) in
    let res = res.[res_i] <- inputi in
    res
  ) res

val text_to_nat:
  len:size_pos{8 * (blocks len 8) < max_size_t} -> input:bytes_i len ->
  Tot (bignum_i (blocks len 8))
let text_to_nat len input =
  let num_words = blocks len 8 in
  let tmpLen = 8 * num_words in
  let m = len % 8 in
  let ind = if (m = 0) then 0 else 8 - m in
  let tmp = create tmpLen (u8 0) in
  let tmpLen' = tmpLen - ind in
  let res = create num_words (u64 0) in
  let tmp = update_sub tmp ind tmpLen' input in
  text_to_nat_ tmpLen tmp num_words res

val nat_to_text_:
  len:size_pos -> input:bignum_i len ->
  resLen:size_pos{resLen = 8 * len} -> res:bytes_i resLen -> Tot (bytes_i resLen)
let nat_to_text_ len input resLen res =
  repeati len
  (fun i res ->
    let ind = len - i - 1 in
    let tmp = input.[ind] in
    let tmp_bytes = uint_to_bytes_be tmp in
    let res = update_sub res (8 * i) 8 tmp_bytes in
    res
  ) res

val nat_to_text:
  len:size_pos ->
  input:bignum_i (blocks len 8){8 * (blocks len 8) < max_size_t} ->
  Tot (lbytes len)
let nat_to_text len input =
  let num_words = blocks len 8 in
  let tmpLen = 8 * num_words in
  let m = len % 8 in
  let ind = if (m = 0) then 0 else 8 - m in

  let tmp = create tmpLen (u8 0) in
  let tmp = nat_to_text_ num_words input tmpLen tmp in
  let tmpLen1 = tmpLen - ind in
  let tmp1 = sub tmp ind tmpLen1 in
  tmp1
