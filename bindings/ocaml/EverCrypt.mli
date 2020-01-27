open Shared

module AutoConfig2 : sig
  val has_shaext : unit -> bool
  val has_aesni : unit -> bool
  val has_pclmulqdq : unit -> bool
  val has_avx2 : unit -> bool
  val has_avx : unit -> bool
  val has_bmi2 : unit -> bool
  val has_adx : unit -> bool
  val has_sse : unit -> bool
  val has_movbe : unit -> bool
  val has_rdrand : unit -> bool
  val wants_vale : unit -> bool
  val wants_hacl : unit -> bool
  val wants_openssl : unit -> bool
  val wants_bcrypt : unit -> bool
  val recall : unit -> unit
  val init : unit -> unit
  val disable_avx2 : unit -> unit
  val disable_avx : unit -> unit
  val disable_bmi2 : unit -> unit
  val disable_adx : unit -> unit
  val disable_shaext : unit -> unit
  val disable_aesni : unit -> unit
  val disable_pclmulqdq : unit -> unit
  val disable_sse : unit -> unit
  val disable_movbe : unit -> unit
  val disable_rdrand : unit -> unit
  val disable_vale : unit -> unit
  val disable_hacl : unit -> unit
  val disable_openssl : unit -> unit
  val disable_bcrypt : unit -> unit
end

module Error : sig
  type error_code =
    | UnsupportedAlgorithm
    | InvalidKey
    | AuthenticationFailure
    | InvalidIVLength
    | DecodeError
  type 'a result =
    | Success of 'a
    | Error of error_code
end

module AEAD : sig
  type t
  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305
  val init : alg -> Bigstring.t -> t Error.result
  val encrypt : t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit Error.result
  val decrypt : t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit Error.result
end

module Chacha20_Poly1305 : Chacha20_Poly1305

module Curve25519 : Curve25519

module Hash : sig
  type t
  type alg =
    | SHA2_224
    | SHA2_256
    | SHA2_384
    | SHA2_512
  val init : alg -> t
  val update : t -> Bigstring.t -> unit
  val finish : t -> Bigstring.t -> unit
  val free : t -> unit
  val hash : alg -> Bigstring.t -> Bigstring.t -> unit
end

module SHA2_224 : Hash

module SHA2_256 : Hash
