module Hacl.SHA1

open Spec.Hash.Helpers
include Hacl.Hash.Common // to appear last, because of update_t

module U8 = FStar.UInt8
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.SHA1

val alloca: alloca_st SHA1

val init: init_st SHA1

val update: update_st SHA1

val pad: pad_st SHA1
