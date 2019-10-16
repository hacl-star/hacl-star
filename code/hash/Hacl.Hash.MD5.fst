module Hacl.Hash.MD5

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.MD5

friend Hacl.Hash.MD

let legacy_update_multi: update_multi_st MD5 = Hacl.Hash.MD.mk_update_multi MD5 legacy_update
let legacy_update_last: update_last_st MD5 = Hacl.Hash.MD.mk_update_last MD5 legacy_update_multi legacy_pad
let legacy_hash: hash_st MD5 = Hacl.Hash.MD.mk_hash MD5 legacy_alloca legacy_update_multi legacy_update_last legacy_finish
