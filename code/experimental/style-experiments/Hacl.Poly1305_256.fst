module Hacl.Poly1305_256
open Hacl.Impl.Poly1305.Fields
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

let ctxlen = size 480
let blocklen = size 16
type poly1305_ctx = lbuffer Lib.Vec256.vec256 30
  
let poly1305_mac o t l k = Hacl.Impl.Poly1305.poly1305_mac #M256 o t l k

