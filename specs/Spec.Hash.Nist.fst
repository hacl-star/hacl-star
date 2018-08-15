module Spec.Hash.Nist

open Spec.Hash.Helpers
open Spec.Hash

module S = FStar.Seq

(* This one is close to the NIST standard. *)
let hash (a:hash_alg) (input:bytes{S.length input < max_input8 a}):
  Tot (hash:bytes{Seq.length hash = size_hash a})
=
  let blocks = pad a (S.length input) in
  finish a (update_multi a (init a) S.(input @| blocks))
