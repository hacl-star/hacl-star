module Hacl.Hash.SHA1

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.SHA1

friend Hacl.Hash.MD

let update_multi: update_multi_st SHA1 = Hacl.Hash.MD.mk_update_multi SHA1 update
let update_last: update_last_st SHA1 = Hacl.Hash.MD.mk_update_last SHA1 update_multi pad
let hash: hash_st SHA1 = Hacl.Hash.MD.mk_hash SHA1 alloca update_multi update_last finish
