module Hacl.Hash.MD5

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.MD5

val legacy_update_multi: update_multi_st MD5
val legacy_update_last: update_last_st MD5
val legacy_hash: hash_st MD5
