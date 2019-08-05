module Hacl.NaCl

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module SB = Spec.Box
module SS = Spec.SecretBox


#set-options "--max_fuel 50 --max_fuel 0 --max_ifuel 0"

val crypto_secretbox_detached:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
    (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == SS.secretbox_detached (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))

let crypto_secretbox_detached c tag m mlen n k =
  Hacl.Impl.SecretBox.secretbox_detached mlen c tag k n m;
  0ul


val crypto_secretbox_open_detached:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SS.secretbox_open_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_secretbox_open_detached m c tag mlen n k =
  Hacl.Impl.SecretBox.secretbox_open_detached mlen m k n c tag


val crypto_secretbox_easy:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    as_seq #MUT #uint8 #(mlen +! 16ul) h1 c ==
      SS.secretbox_easy (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))

let crypto_secretbox_easy c m mlen n k =
  Hacl.Impl.SecretBox.secretbox_easy mlen c k n m;
  0ul


#set-options "--z3rlimit 100"

val crypto_secretbox_open_easy:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SS.secretbox_open_easy (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_secretbox_open_easy m c clen n k =
  Hacl.Impl.SecretBox.secretbox_open_easy (clen -! 16ul) m k n c


val crypto_box_beforenm:
    k:lbuffer uint8 32ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h -> live h k /\ live h pk /\ live h sk /\
    disjoint k pk /\ disjoint k sk)
  (ensures  fun h0 r h1 -> modifies1 k h0 h1 /\
   (let key = SB.box_beforenm (as_seq h0 pk) (as_seq h0 sk) in
    match r with
    | 0ul -> Some? key /\ as_seq h1 k == Some?.v key
    | _ -> None? key))

let crypto_box_beforenm k pk sk =
  Hacl.Impl.Box.box_beforenm k pk sk


val crypto_box_detached_afternm:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
    (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == SB.box_detached_afternm (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))

let crypto_box_detached_afternm c tag m mlen n k =
  Hacl.Impl.Box.box_detached_afternm mlen c tag k n m


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
   (let tag_cipher = SB.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? tag_cipher /\ (let (tag_s, cipher_s) = Some?.v tag_cipher in (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == (tag_s, cipher_s))
    | _ -> None? tag_cipher))

let crypto_box_detached c tag m mlen n pk sk =
  Hacl.Impl.Box.box_detached mlen c tag sk pk n m


val crypto_box_open_detached_afternm:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SB.box_open_detached_afternm (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_box_open_detached_afternm m c tag mlen n k =
  Hacl.Impl.Box.box_open_detached_afternm mlen m k n c tag


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
   (let msg = SB.box_open_detached (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_box_open_detached m c tag mlen n pk sk =
  Hacl.Impl.Box.box_open_detached mlen m pk sk n c tag


val crypto_box_easy_afternm:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    as_seq #MUT #uint8 #(mlen +! 16ul) h1 c ==
      SB.box_easy_afternm (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))

let crypto_box_easy_afternm c m mlen n k =
  Hacl.Impl.Box.box_easy_afternm mlen c k n m


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
    (let cipher = SB.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? cipher /\ as_seq #MUT #uint8 #(mlen +! 16ul) h1 c == Some?.v cipher
    | _ -> None? cipher))

let crypto_box_easy c m mlen n pk sk =
  Hacl.Impl.Box.box_easy mlen c sk pk n m


val crypto_box_open_easy_afternm:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SB.box_open_easy_afternm (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_box_open_easy_afternm m c clen n k =
  Hacl.Impl.Box.box_open_easy_afternm (clen -! 16ul) m k n c


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
   (let msg = SB.box_open_easy (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

let crypto_box_open_easy m c clen n pk sk =
  Hacl.Impl.Box.box_open_easy (clen -! 16ul) m pk sk n c
