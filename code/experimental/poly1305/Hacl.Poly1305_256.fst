module Hacl.Poly1305_256
open Hacl.Impl.Poly1305.Fields
open Lib.IntTypes
open Lib.Buffer

let ctxlen = size 480
let blocklen = size 16
type poly1305_ctx = lbuffer Lib.Vec256.vec256 30ul

let poly1305_init (ctx:poly1305_ctx) (key:lbuffer uint32 32ul) = 
    Hacl.Impl.Poly1305.poly1305_init #M256 ctx key
let poly1305_update_blocks (ctx:poly1305_ctx) (len:size_t{v len % v blocklen == 0}) (text:lbuffer uint8 len) =
    Hacl.Impl.Poly1305.poly1305_update #M256 ctx len text 
let poly1305_update_padded (ctx:poly1305_ctx) (len:size_t) (text:lbuffer uint8 len) =
    Hacl.Impl.Poly1305.poly1305_update #M256 ctx len text 
let poly1305_update_last (ctx:poly1305_ctx) (len:size_t{v len < 16}) (text:lbuffer uint8 len) =
    Hacl.Impl.Poly1305.poly1305_update #M256 ctx len text
let poly1305_finish (ctx:poly1305_ctx) (tag:lbuffer uint8 16ul) = 
    Hacl.Impl.Poly1305.poly1305_finish #M256 ctx tag
  
let poly1305_mac (o:lbuffer uint8 16ul) (t:buffer uint8) (l:size_t{length t == v l}) (k:lbuffer uint8 32ul) = Hacl.Impl.Poly1305.poly1305_mac #M256 o l t k


