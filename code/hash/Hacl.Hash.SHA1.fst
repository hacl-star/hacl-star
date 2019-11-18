module Hacl.Hash.SHA1

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.SHA1

friend Hacl.Hash.MD

let legacy_update_multi: update_multi_st SHA1 = Hacl.Hash.MD.mk_update_multi SHA1 legacy_update
let legacy_update_last: update_last_st SHA1 = Hacl.Hash.MD.mk_update_last SHA1 legacy_update_multi legacy_pad
let legacy_hash: hash_st SHA1 = Hacl.Hash.MD.mk_hash SHA1 legacy_alloca legacy_update_multi legacy_update_last legacy_finish
