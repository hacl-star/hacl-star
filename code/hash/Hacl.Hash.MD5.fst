module Hacl.Hash.MD5

open Hacl.Hash.Definitions
open Spec.Hash.Definitions

include Hacl.Hash.Core.MD5

friend Hacl.Hash.MD

let update_multi: update_multi_st MD5 = Hacl.Hash.MD.mk_update_multi MD5 update
let update_last: update_last_st MD5 = Hacl.Hash.MD.mk_update_last MD5 update_multi pad
let hash: hash_st MD5 = Hacl.Hash.MD.mk_hash MD5 alloca update_multi update_last finish
