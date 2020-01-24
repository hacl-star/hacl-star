open Unsigned

open Shared

module Chacha20_Poly1305_32 : Chacha20_Poly1305
module Chacha20_Poly1305_128 : Chacha20_Poly1305
module Chacha20_Poly1305_256 : Chacha20_Poly1305

module Curve25519_51 : Curve25519
module Curve25519_64 : Curve25519
module Curve25519_64_Slow : Curve25519

module Curve25519_51_Internal : sig
  include Curve25519
  val fadd : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val fsub : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val fmul1 : Bigstring.t -> Bigstring.t -> uint64 -> unit
end
