module Spec.HKDF

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module Hash = Spec.Hash
module HMAC = Spec.HMAC


(* val hkdf_extract_core: *)
(*     a:Hash.algorithm *)
(*   -> salt:lbytes (Hash.size_block a) *)
(*   -> len_ikm:size_nat{Hash.size_block a + len_ikm < max_size_t /\ Hash.size_block a + len_ikm < Hash.max_input a} *)
(*   -> ikm:lbytes len_ikm -> *)
(*   Tot (lbytes (Hash.size_hash a)) *)

(* val hkdf_extract: *)
(*     a:Hash.algorithm *)
(*   -> len_salt:size_nat{len_salt < Hash.max_input a} *)
(*   -> salt:lbytes len_salt *)
(*   -> len_ikm:size_nat{Hash.size_block a + len_ikm < max_size_t /\ Hash.size_block a + len_ikm < Hash.max_input a} *)
(*   -> ikm:lbytes len_ikm -> *)
(*   Tot (lbytes (Hash.size_hash a)) *)

(* val hkdf_expand: *)
(*     a:Hash.algorithm *)
(*   -> len_prk:size_nat{len_prk < Hash.max_input a} *)
(*   -> prk:lbytes len_prk *)
(*   -> len_info:size_nat{Hash.size_block a + Hash.size_hash a + len_info + 1 < max_size_t /\ Hash.size_block a + Hash.size_hash a + len_info + 1 < Hash.max_input a} *)
(*   -> info:lbytes len_info *)
(*   -> len:size_nat{len < 255 * Hash.size_hash a} -> *)
(*   Tot (lbytes len) *)
