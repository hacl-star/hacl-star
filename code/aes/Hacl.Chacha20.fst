module Hacl.Chacha20

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

let chacha20_encrypt out text len key n ctr = Hacl.Impl.Chacha20.chacha20_encrypt out text len key n ctr
let chacha20_decrypt out text len key n ctr = Hacl.Impl.Chacha20.chacha20_decrypt out text len key n ctr
