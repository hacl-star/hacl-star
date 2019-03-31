module EverCrypt.Cipher

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

(*
// JP: ideally, we'd like a signature along those lines:

val chacha20: dst:B.buffer U8.t ->
  len:U32.t { U32.v len = B.length dst } ->
  src:B.buffer U8.t { B.length src = B.length dst } ->
  key:B.buffer U8.t { B.length key = 32 } ->
  iv:B.buffer U8.t { B.length iv = 12 } ->
  ctr:U32.t -> FStar.HyperStack.ST.Stack unit
    (requires (fun h ->
      B.live h key /\ B.live h iv /\ B.live h src /\ B.live h dst /\
      (B.disjoint src dst \/ src == dst) /\
      U32.v ctr + U32.v len / 64 <= FStar.UInt.max_int 32))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      B.as_seq h1 dst == Spec.Chacha20.chacha20_encrypt_bytes
        (B.as_seq h0 key) (B.as_seq h0 iv) (U32.v ctr) (B.as_seq h0 src)))

// But we can't do that currently because Spec.Chacha20 is in terms of
// Lib.IntTypes. A possible fix would be to add an interface on top of
// Spec.Chacha20, then perhaps re-export Spec.Chacha20 with i) "classic" integer
// types from ulib and ii) a spec that makes the CTR construction apparent.

// This is, however, a non-trivial piece of work, so for the time being, we take
// whatever spec is currently in there, i.e. the HACL* spec with Lib.*.
*)

(** @type: true
*)
val chacha20: len:size_t ->
  dst:lbuffer uint8 len ->
  src:lbuffer uint8 len ->
  key:lbuffer uint8 32ul ->
  iv:lbuffer uint8 12ul ->
  ctr:size_t -> ST.Stack unit
		  (requires (fun h ->
        live h key /\ live h iv /\ live h src /\ live h dst /\
        eq_or_disjoint src dst /\ v ctr + v len / 64 <= max_size_t ))
		  (ensures (fun h0 _ h1 ->
        modifies (loc dst) h0 h1 /\
        as_seq h1 dst ==
          Spec.Chacha20.chacha20_encrypt_bytes
            (as_seq h0 key) (as_seq h0 iv) (v ctr) (as_seq h0 src)))
