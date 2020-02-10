module type Chacha20_Poly1305 = sig
  val encrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val decrypt: Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module type Curve25519 = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val scalarmult : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val ecdh : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
end

module type EdDSA = sig
  val secret_to_public : Bigstring.t -> Bigstring.t -> unit
  val sign : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val verify : Bigstring.t -> Bigstring.t -> Bigstring.t -> bool
  val expand_keys : Bigstring.t -> Bigstring.t -> unit
  val sign_expanded : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module type HashFunction = sig
  val hash : Bigstring.t -> Bigstring.t -> unit
end

module type MAC = sig
  val mac : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module type HKDF = sig
  val expand: Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
  val extract: Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

module type Blake2b = sig
  val hash : Bigstring.t -> Bigstring.t -> Bigstring.t -> unit
end

