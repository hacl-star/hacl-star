module Mem

open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Index
open Box.Plain


module MM = FStar.Monotonic.Map

type message_log_key (nonce:Type0) (ciphertext:Type0) = inst_id*nonce*ciphertext
//  | LOG_KEY: i:inst_id -> n:nonce aparams -> c:ciphertext aparams -> message_log_key aparams

let message_log_value (pp:plain_package) (i:inst_id) = protected_plain pp i
let message_log_range (#nonce:Type0) (#ciphertext:Type0) (pp:plain_package)  (k:message_log_key nonce ciphertext) = message_log_value pp (Mktuple3?._1 k)
let message_log_inv (#nonce:Type0) (#ciphertext:Type0) (#pp:plain_package) (f:MM.map' (message_log_key nonce ciphertext) (message_log_range pp)) = True

let message_log (nonce:Type0) (ciphertext:Type0) (pp:plain_package) (rgn:erid) =
  MM.t rgn (message_log_key nonce ciphertext) (message_log_range pp) (message_log_inv)

let empty_message_log (nonce:Type0) (ciphertext:Type0) (pp:plain_package) = MM.empty_map (message_log_key nonce ciphertext) (message_log_range pp)

let alloc_message_log (nonce:Type0) (ciphertext:Type0) (rgn:erid) (pp:plain_package) = MM.alloc #rgn #(message_log_key nonce ciphertext) #(message_log_range pp) #(message_log_inv)
