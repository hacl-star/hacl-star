module Hacl.NaCl.Box

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module Spec = Spec.Box
module LibSeq = Lib.Sequence

val crypto_box_detached: c:buffer uint8 -> tag:lbuffer uint8 16ul -> m:buffer uint8 ->
			 mlen:size_t{length c = v mlen /\ length m = v mlen} ->
			 n:lbuffer uint8 24ul -> pk:lbuffer uint8 32ul -> sk:lbuffer uint8 32ul ->
   			 Stack size_t
			 (requires (fun h -> live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\ live h tag /\
					  disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen)))
			 (ensures (fun h0 _ h1 -> modifies (loc c |+| loc tag) h0 h1))
			(*
			/\
			  (as_seq h1 tag,as_seq h1 c) ==
			   Spec.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m))) *)
#set-options "--z3rlimit  300"
let crypto_box_detached c tag m mlen n pk sk =
  Hacl.Impl.Box.box_detached mlen c tag sk pk n m;
  0ul



val crypto_box_open_detached: m:buffer uint8 -> c:buffer uint8 -> tag:lbuffer uint8 16ul ->
			 mlen:size_t{length c = v mlen /\ length m = v mlen} ->
			 n:lbuffer uint8 24ul -> pk:lbuffer uint8 32ul -> sk:lbuffer uint8 32ul ->
			Stack size_t
			(requires (fun h -> live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\ live h tag /\
				   disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen)))
			(ensures (fun h0 _ h1 -> modifies (loc m) h0 h1))
			(*
			/\
			  (as_seq h1 tag,as_seq h1 m) ==
			   Spec.box_open_detached (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 tag) (as_seq h0 c))) *)
let crypto_box_open_detached m c tag mlen n pk sk =
    Hacl.Impl.Box.box_open_detached mlen m pk sk n c tag

val crypto_box_easy: c:buffer uint8 -> m:buffer uint8 ->
		     mlen:size_t{length c = v mlen + 16 /\ length m = v mlen} ->
		     n:lbuffer uint8 24ul -> pk:lbuffer uint8 32ul -> sk:lbuffer uint8 32ul ->
 		     Stack size_t
		     (requires (fun h -> live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\
				      disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen)))
		     (ensures (fun h0 _ h1 -> modifies (loc c) h0 h1))
			(*
			/\
			  as_seq h1 c ==
			   Spec.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m))) *)
let crypto_box_easy c m mlen n pk sk =
  Hacl.Impl.Box.box_easy mlen c sk pk n m;
  0ul


val crypto_box_open_easy: m:buffer uint8 -> c:buffer uint8 ->
			 mlen:size_t{length c = v mlen + 16 /\ length m = v mlen} ->
			 n:lbuffer uint8 24ul -> pk:lbuffer uint8 32ul -> sk:lbuffer uint8 32ul ->
			Stack size_t
			(requires (fun h -> live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
				   disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen)))
			(ensures (fun h0 _ h1 -> modifies (loc m) h0 h1))
			(*
			/\
			   as_seq h1 m ==
			   Spec.box_open_easy (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 c))) *)
let crypto_box_open_easy m c mlen n pk sk =
    Hacl.Impl.Box.box_open_easy mlen m pk sk n c 


