module Spec.SHA512

open Spec.SHA2_512

#reset-options "max_fuel 0 --z3rlimit 20"

let k = k
let h_0 = h_0
let update h b = update h b
let update_multi h b = update_multi h b
let update_last h l i = update_last h l i
let finish h = finish h
let hash s = hash s
