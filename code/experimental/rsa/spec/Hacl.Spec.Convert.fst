module Hacl.Spec.Convert

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.Endian
open Hacl.Spec.Lib


val text_to_nat_:
  len:size_nat{len > 0} ->
  input:lbytes len ->
  resLen:size_nat{len = 8 * resLen} ->
  res:lseqbn resLen ->
  i:size_nat{i <= resLen} -> Tot (lseqbn resLen)
  (decreases (resLen - i))
let rec text_to_nat_ len input resLen res i =
  if (i < resLen) then begin
    let inputi = uint_from_bytes_be #U64 (sub input (8 * i) 8) in
    let ind = resLen - i - 1 in
    let res = res.[ind] <- inputi in
    text_to_nat_ len input resLen res (i + 1)
  end else res

val text_to_nat:
  len:size_nat{len > 0} ->
  input:lbytes len ->
  res:lseqbn (get_size_nat len){8 * (get_size_nat len) < max_size_t} -> Tot (lseqbn (get_size_nat len))
let text_to_nat len input res =
  let num_words = get_size_nat len in
  let tmpLen:size_nat = 8 * num_words in
  let m = len % 8 in
  let ind = if (m = 0) then 0 else 8 - m in
  let tmp = create tmpLen (u8 0) in
  let tmpLen' = tmpLen - ind in
  assume (tmpLen' = len);
  let tmp = update_sub tmp ind tmpLen' input in
  text_to_nat_ tmpLen tmp num_words res 0

val nat_to_text_:
  len:size_nat{len > 0} ->
  input:lseqbn len ->
  resLen:size_nat{resLen = 8 * len} ->
  res:lbytes resLen ->
  i:size_nat{i <= len} -> Tot (lbytes resLen)
  (decreases (len - i))
let rec nat_to_text_ len input resLen res i =
  if (i < len) then begin
    let ind = len - i - 1 in
    let tmp = input.[ind] in
    let tmp_bytes = uint_to_bytes_be tmp in
    let res = update_sub res (8 * i) 8 tmp_bytes in
    nat_to_text_ len input resLen res (i + 1)
  end else res

val nat_to_text:
  len:size_nat{len > 0} ->
  input:lseqbn (get_size_nat len){8 * (get_size_nat len) < max_size_t} ->
  res:lbytes len -> Tot (lbytes len)
let nat_to_text len input res =
  let num_words = get_size_nat len in
  let tmpLen:size_nat = 8 * num_words in
  let m = len % 8 in
  let ind = if (m = 0) then 0 else 8 - m in
  let tmp = create tmpLen (u8 0) in
  let tmp = nat_to_text_ num_words input tmpLen tmp 0 in
  let tmpLen' = tmpLen - ind in
  assume (tmpLen' = len);
  let tmp' = sub tmp ind tmpLen' in
  let res = update_sub res 0 len tmp' in res
