module AEAD : sig
  type t
  type alg =
    | AES128_GCM
    | AES256_GCM
    | CHACHA20_POLY1305
  type result =
    | Error of int
    | Success
  val alloc_t : unit -> t
  val create_in : alg -> t -> Bigstring.t -> result
  val encrypt : t -> Bigstring.t -> int -> Bigstring.t -> int -> Bigstring.t -> int -> Bigstring.t -> Bigstring.t -> result
  val decrypt : t -> Bigstring.t -> int -> Bigstring.t -> int -> Bigstring.t -> int -> Bigstring.t -> Bigstring.t -> result
end
