module Mem

open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Index
open Box.Plain


module MM = FStar.Monotonic.Map
module Flags = Box.Flags

// Merge this file with plain?

type message_log_key (ip:index_package) (pp:plain_package) = id ip*nonce pp*cipher pp
//  | LOG_KEY: i:id ip -> n:nonce aparams -> c:ciphertext aparams -> message_log_key aparams

let message_log_value (#ip:index_package) (pp:plain_package) (i:id ip) = protected_plain pp i
let message_log_range (#ip:index_package)(pp:plain_package)  (k:message_log_key ip pp) = message_log_value pp (Mktuple3?._1 k)
let message_log_inv (#ip:index_package) (#pp:plain_package) (f:MM.map' (message_log_key ip pp) (message_log_range pp)) = True

let i_message_log (ip:index_package) (pp:plain_package) (rgn:erid) =
  MM.t rgn (message_log_key ip pp) (message_log_range pp) (message_log_inv)
let message_log (ip:index_package) (pp:plain_package) (rgn:erid) =
  if Flags.model then
    MM.t rgn (message_log_key ip pp) (message_log_range pp) (message_log_inv)
  else
   unit

let empty_message_log (ip:index_package) (pp:plain_package) = MM.empty_map (message_log_key ip pp) (message_log_range pp)

let alloc_message_log (rgn:erid) (ip:index_package) (pp:plain_package) = MM.alloc #rgn #(message_log_key ip pp) #(message_log_range pp) #(message_log_inv)
