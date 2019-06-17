module EverCrypt.Cipher

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST

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
