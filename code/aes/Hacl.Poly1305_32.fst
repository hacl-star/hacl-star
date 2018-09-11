module Hacl.Poly1305_32
open Hacl.Impl.Poly1305.Fields
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
let ctxlen = size 20
let blocklen = size 16
type poly1305_ctx = lbuffer uint32 20

let poly1305_init (ctx:poly1305_ctx) (key:lbytes 32) = 
    Hacl.Impl.Poly1305.poly1305_init #M32 ctx key
let poly1305_update (ctx:poly1305_ctx) (text:bytes) 
		    (len:size_t{size_v len == length text /\ size_v len % size_v blocklen = 0}) = 
    Hacl.Impl.Poly1305.poly1305_update #M32 ctx text len
let poly1305_finish (ctx:poly1305_ctx) (tag:lbytes 16) = 
    Hacl.Impl.Poly1305.poly1305_finish #M32 ctx tag
  
let poly1305_mac o t l k = Hacl.Impl.Poly1305.poly1305_mac #M32 o t l k
