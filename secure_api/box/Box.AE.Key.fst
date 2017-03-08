(**
   This module exists to provide type information and functions needed by Box.DH. Box.AE is not imported directly by
   Box.DH to preserve some notion of modularity. If Box.DH should be used with some other module, only Box.PlainDH
   should have to be edited.
*)
module Box.AE.Key

module AE = Box.AE

type key = AE.key

let ae_key_get_index = AE.get_index

let keygen = AE.keygen

let coerce_key = AE.coerce_key

let leak_key = AE.leak_key

let ae_key_region = AE.ae_key_region

let get_logGT = AE.get_logGT

let recall_log = AE.recall_log

let empty_log = AE.empty_log

let aes_key = AE.aes_key
