module Hacl.NaCl

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module Spec = Spec.Box
module LSeq = Lib.Sequence


#set-options "--max_fuel 50 --max_fuel 0 --max_ifuel 0"

val crypto_box_detached:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
   (let tag_cipher = Spec.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? tag_cipher /\ (let (tag_s, cipher_s) = Some?.v tag_cipher in (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == (tag_s, cipher_s))
    | _ -> None? tag_cipher))

let crypto_box_detached c tag m mlen n pk sk =
  Hacl.Impl.Box.box_detached mlen c tag sk pk n m


val crypto_box_open_detached:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = Spec.box_open_detached (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_box_open_detached m c tag mlen n pk sk =
  Hacl.Impl.Box.box_open_detached mlen m pk sk n c tag


val crypto_box_easy:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    (let cipher = Spec.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? cipher /\ as_seq #MUT #uint8 #(mlen +! 16ul) h1 c == Some?.v cipher
    | _ -> None? cipher))

let crypto_box_easy c m mlen n pk sk =
  Hacl.Impl.Box.box_easy mlen c sk pk n m


#set-options "--z3rlimit 100"

val crypto_box_open_easy:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = Spec.box_open_easy (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_box_open_easy m c clen n pk sk =
  Hacl.Impl.Box.box_open_easy (clen -! 16ul) m pk sk n c
