module Spec.HKDF

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

open Spec.SHA2
open Spec.HMAC

#reset-options "--z3rlimit 50 --max_fuel 0"

module Hash = Spec.SHA2
module HMAC = Spec.HMAC

let hkdf_extract_core
  (p:Hash.parameters)
  (salt:lbytes (Hash.size_block p))
  (len_ikm:size_t{Hash.size_block p + len_ikm < max_size_t /\ Hash.size_block p + len_ikm < Hash.maxInput p})
  (ikm:lbytes len_ikm) =
  HMAC.hmac_core p salt len_ikm ikm

let hkdf_extract
  (p:Hash.parameters)
  (len_salt:size_t)
  (salt:lbytes len_salt)
  (len_ikm:size_t{Hash.size_block p + len_ikm < max_size_t /\ Hash.size_block p + len_ikm < Hash.maxInput p})
  (ikm:lbytes len_ikm) =
  if len_salt = 0 then
    let salt = create (p.size_hash) (u8 0) in
    HMAC.hmac p p.size_hash salt len_ikm ikm
  else
    HMAC.hmac p len_salt salt len_ikm ikm

let hkdf_expand (p:Hash.parameters) (len_prk:size_t) (prk:lbytes len_prk) (len_info:size_t{p.size_hash + len_info + 1 < max_size_t}) (info:lbytes len_info) (len:size_t{len <= 255 `op_Multiply` p.size_hash}) =
  assume(p.size_hash <> 0);
  let n : size_t = len / p.size_hash + 1 in
  let _T = create (n * p.size_hash) (u8 0) in
  let tic = create (p.size_hash + len_info + 1) (u8 0) in
  let tic = update_slice tic p.size_hash (p.size_hash + len_info) info in
  let _T = repeat_range 1 (n + 1) (fun i t ->
    let pos_ni_sub2 = (i - 2) * p.size_hash in
    let pos_ni_sub1 = (i - 1) * p.size_hash in
    let pos_ni = i * p.size_hash in
    let ti =
      if i = 1 then begin
        let tic = tic.[p.size_hash + len_info] <- u8 i in
        let tic = slice tic p.size_hash (p.size_hash + len_info + 1) in
        HMAC.hmac p len_prk prk (len_info + 1) tic end
      else begin
        let ti_prev = slice t pos_ni_sub2 pos_ni_sub1 in
        let tic = update_slice tic 0 p.size_hash ti_prev in
        let tic = tic.[p.size_hash + len_info] <- u8 i in
        HMAC.hmac p len_prk prk (p.size_hash + len_info + 1) tic end in
    update_slice t pos_ni_sub1 pos_ni ti) _T
  in
  slice _T 0 len
