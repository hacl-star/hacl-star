module Box.PKAE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain

module AE = Box.AE
module ODH = Box.ODH
module MM = FStar.Monotonic.Map
module SPEC = Spec.SecretBox

let id = ODH.id
assume val random_bytes: n:(n:nat{n<=32}) -> unit -> lbytes n

let secretbox_scheme =
  AE.ES (random_bytes 32) SPEC.secretbox_easy SPEC.secretbox_open_easy

let ae_package_log_key = i:id
let ae_package_log_value (i:id)  = ae_package
let ae_package_log_range (#id:eqtype) (i:id) (pp:plain_package) (nonce_length:(n:nat{n<=32})) (k:message_log_key nonce_length) = message_log_value i pp
let ae_package_log_inv (#pp:plain_package) (#nonce_length:(n:nat{n<=32})) (#id:eqtype) (i:id) (f:MM.map' (message_log_key nonce_length) (message_log_range i pp nonce_length)) = True

let message_log (#pp:plain_package) (#id:eqtype) (rgn:erid) (nonce_length:(n:nat{n<=32})) (i:id) =
  MM.t rgn (message_log_key nonce_length) (message_log_range i pp nonce_length) (message_log_inv i)

//noeq abstract type pkae_package =
//  | PKAE_P :


let gen = ODH.gen_dh
