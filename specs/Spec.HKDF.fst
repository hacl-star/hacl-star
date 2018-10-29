module Spec.HKDF

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module Hash = Spec.Hash
module HMAC = Spec.HMAC


(* val hkdf_extract: *)
(*     a:Hash.algorithm *)
(*   -> salt: bytes{length salt <= Hash.max_input a} *)
(*   -> ikm: bytes{length salt + length ikm + Hash.size_block a <= Hash.max_input a *)
(*         /\ Hash.size_hash a + length ikm + Hash.size_block a <= Hash.max_input a} -> *)
(*   Tot (lbytes (Hash.size_hash a)) *)

let hkdf_extract a salt ikm =
  let slen = length salt in
  if slen = 0 then
    let salt0 = create (Hash.size_hash a) (u8 0) in
    HMAC.hmac a salt0 ikm
  else
    HMAC.hmac a salt ikm


val hkdf_round0:
    a: Hash.algorithm
  -> prk: bytes{length prk <= Hash.max_input a}
  -> info: bytes{length info + Hash.size_hash a + 1 <= max_size_t (* BB. FIXME, this is required by create *)
              /\ length prk + length info + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a} ->
  Tot (lbytes (Hash.size_hash a))

let hkdf_round0 a prk info =
  let ilen = length info in
  let input = create (ilen + 1) (u8 0) in
  let input = update_sub input 0 ilen info in
  let input = input.[ilen] <- u8 1 in
  HMAC.hmac a prk input


val hkdf_round:
    a: Hash.algorithm
  -> prk: bytes{length prk <= Hash.max_input a}
  -> info: bytes{length info + Hash.size_hash a + 1 <= max_size_t (* BB. FIXME, this is required by create *)
              /\ length prk + length info + 1 + Hash.size_hash a + Hash.size_block a <= Hash.max_input a}
  -> i:nat{1 < i /\ i <= 255}
  -> ti:lbytes (Hash.size_hash a) ->
  Tot (lbytes (Hash.size_hash a))

let hkdf_round a prk info i ti =
  let ilen = length info in
  let input = create (Hash.size_hash a + ilen + 1) (u8 0) in
  let input = update_sub input 0 (Hash.size_hash a) ti in
  let input = update_sub input (Hash.size_hash a) ilen info in
  let input = input.[(Hash.size_hash a) + ilen] <- u8 i in
  HMAC.hmac a prk input


let hkdf_expand a prk info len =
  let n : size_nat = len / (Hash.size_hash a) + 1 in
  let t = create #uint8 (n * Hash.size_hash a) (u8 0) in
  (* Compute T(0) *)
  let t0 = hkdf_round0 a prk info in
  let t = update_sub t 0 (Hash.size_hash a) t0 in
  (* Compute T(1) ... T(N)*)
  let t =
    repeat_range 2 (n + 1)
      (fun i t ->
        let ti = sub t ((i - 2) * Hash.size_hash a) (Hash.size_hash a) in
        let r = hkdf_round a prk info i ti in
        update_sub t ((i - 1) * Hash.size_hash a) (Hash.size_hash a) r
      ) t in
  let res = sub t 0 len in
  res
