module Hacl.MD5

open Spec.Hash.Helpers
include Hacl.Hash.Common // must come last, for update_t

module U8 = FStar.UInt8
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Spec = Spec.MD5

val alloca: alloca_st MD5

val init: init_st MD5

val update: update_st MD5

val pad: pad_st MD5

val finish: finish_st MD5
