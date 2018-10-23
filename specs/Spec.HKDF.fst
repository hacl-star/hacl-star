module Spec.HKDF

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
#reset-options "--z3rlimit 250 --max_fuel 0"

module Hash = Spec.Hash
module HMAC = Spec.HMAC


let hkdf_extract
  (a:Hash.algorithm)
  (len_salt:size_nat{len_salt <= Hash.max_input a})
  (salt:lbytes len_salt)
  (len_ikm:size_nat{len_ikm + len_salt + Hash.size_block a <= Hash.max_input a
                  /\ len_ikm + Hash.size_hash a + Hash.size_block a <= Hash.max_input a})
  (ikm:lbytes len_ikm) =

  if len_salt = 0 then
    let salt = create (Hash.size_hash a) (u8 0) in
    HMAC.hmac a (Hash.size_hash a) salt len_ikm ikm
  else
    HMAC.hmac a len_salt salt len_ikm ikm


let hkdf_expand
  (a:Hash.algorithm)
  (len_prk:size_nat{len_prk <= Hash.max_input a})
  (prk:lbytes len_prk)
  (len_info:size_nat{Hash.size_block a + Hash.size_hash a + len_info + 1 <= Hash.max_input a})
  (info:lbytes len_info)
  (len:size_nat{len <= 255 * Hash.size_hash a}) =

  let n : size_nat = len / (Hash.size_hash a) + 1 in
  assert(1 <= n /\ n < 256);
  (* let tlen :size_nat = n * (Hash.size_hash a) in *)
  (* let _T : lbytes tlen = create (n * (Hash.size_hash a)) (u8 0) in *)
  (* let tic = create ((Hash.size_hash a) + len_info + 1) (u8 0) in *)
  (* let tic = update_slice tic (Hash.size_hash a) ((Hash.size_hash a) + len_info) info in *)
  (* let _T = repeat_range 1 (n + 1) (fun i t -> *)
  (*   let pos_ni = i * (Hash.size_hash a) in *)
  (*   let pos_ni_sub1 = (i - 1) * (Hash.size_hash a) in *)
  (*   let ti = *)
  (*     if i = 1 then begin *)
  (*       let tic = tic.[(Hash.size_hash a) + len_info] <- u8 i in *)
  (*       let tic = slice tic (Hash.size_hash a) ((Hash.size_hash a) + len_info + 1) in *)
  (*       HMAC.hmac a len_prk prk (len_info + 1) tic end *)
  (*     else begin *)
  (*       let pos_ni_sub2 = (i - 2) * (Hash.size_hash a) in *)
  (*       let ti_prev = slice t pos_ni_sub2 pos_ni_sub1 in *)
  (*       let tic = update_slice tic 0 (Hash.size_hash a) ti_prev in *)
  (*       let tic = tic.[(Hash.size_hash a) + len_info] <- u8 i in *)
  (*       HMAC.hmac a len_prk prk ((Hash.size_hash a) + len_info + 1) tic end in *)
  (*   update_slice t pos_ni_sub1 pos_ni ti) _T *)
  (* in *)
  (* slice _T 0 len *)
  create len (u8 0)
