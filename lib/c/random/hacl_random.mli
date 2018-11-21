module Lib_RandomSequence : sig
  val write : Bytes.t -> unit
  (** [write buf] writes random bytes on [buf]. *)

  val gen : int -> Bytes.t
  (** [gen len] is a random buffer of length [len]. *)
end
