module Hacl.Chacha20.Vec

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer

val chacha20_encrypt: len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> key:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let chacha20_encrypt len out text key n ctr = Hacl.Impl.Chacha20.Vec.chacha20_encrypt #8 len out text key n ctr


val chacha20_decrypt: len:size_t -> out:lbuffer uint8 len -> text:lbuffer uint8 len -> key:lbuffer uint8 32ul -> n:lbuffer uint8 12ul -> ctr:size_t -> ST unit
		  (requires (fun h -> live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out))
		  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let chacha20_decrypt len out text key n ctr = Hacl.Impl.Chacha20.Vec.chacha20_decrypt #8 len out text key n ctr
