module Hacl.Impl.Ed25519.ExtPoint


(* A point is buffer of size 20, that is 4 consecutive buffers of size 5 *)
let point = b:Buffer.buffer Hacl.Bignum.Parameters.limb{Buffer.length b = 20}

let getx (p:point) : Tot Hacl.Bignum.Parameters.felem = Buffer.sub p 0ul 5ul
let gety (p:point) : Tot Hacl.Bignum.Parameters.felem = Buffer.sub p 5ul 5ul
let getz (p:point) : Tot Hacl.Bignum.Parameters.felem = Buffer.sub p 10ul 5ul
let gett (p:point) : Tot Hacl.Bignum.Parameters.felem = Buffer.sub p 15ul 5ul
