module Spec.Argon2i

#reset-options "--z3rlimit 100 --max_fuel 0"

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

let version_number : uint8 = u8 0x13


val argon2 : 
  p_len:size_nat -> p : lbytes p_len ->
  s_len:size_nat{s_len >= 8} -> s: lbytes s_len ->
  parallel:nat{parallel >= 1 && parallel <= pow2 24 - 1} -> t_len:size_nat{t_len >= 4} -> 
  m_size:size_nat{m_size >= (8 * parallel)} ->
  iterations:size_nat{iterations >= 1}  ->
  k_len:size_nat -> k:lbytes k_len ->
  Tot (lbytes t_len)
