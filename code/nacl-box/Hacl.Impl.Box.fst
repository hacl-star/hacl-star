module Hacl.Impl.Box

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.SecretBox

module ST = FStar.HyperStack.ST
module Spec = Spec.Box
module LSeq = Lib.Sequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val box_beforenm:
    k:lbuffer uint8 32ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h -> live h k /\ live h pk /\ live h sk /\
    disjoint k pk /\ disjoint k sk)
  (ensures  fun h0 r h1 -> modifies (loc k) h0 h1 /\
   (let key = Spec.box_beforenm (as_seq h0 pk) (as_seq h0 sk) in
    match r with
    | 0ul -> Some? key /\ as_seq h1 k == Some?.v key
    | _ -> None? key))

[@CInline]
let box_beforenm k pk sk =
  push_frame();
  let n0 = create 16ul (u8 0) in
  let r = Hacl.Curve25519_51.ecdh k sk pk in
  let res =
    if r then (
      Hacl.Salsa20.hsalsa20 k k n0;
      0ul)
    else
      0xfffffffful in
  pop_frame();
  res


val box_detached_afternm:
    mlen:size_t
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ disjoint tag m /\ eq_or_disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 ->
    modifies (loc c |+| loc tag) h0 h1 /\ r == 0ul /\
    (as_seq h1 tag, as_seq h1 c) == Spec.box_detached_afternm (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))

[@CInline]
let box_detached_afternm mlen c tag k n m =
  secretbox_detached mlen c tag k n m;
  0ul


#set-options "--z3rlimit 100"

val box_detached:
    mlen:size_t
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul
  -> sk:lbuffer uint8 32ul
  -> pk:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\ live h tag /\
    disjoint tag c /\ disjoint tag m /\ eq_or_disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 ->
    modifies (loc c |+| loc tag) h0 h1 /\
    (let tag_cipher = Spec.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m) in
    match r with
    | 0ul -> Some? tag_cipher /\ (let (tag_s, cipher_s) = Some?.v tag_cipher in (as_seq h1 tag, as_seq h1 c) == (tag_s, cipher_s))
    | _ -> None? tag_cipher))

[@CInline]
let box_detached mlen c tag sk pk n m =
  push_frame();
  let k = create 32ul (u8 0) in
  let r = box_beforenm k pk sk in
  let res =
    if r =. size 0 then
      box_detached_afternm mlen c tag k n m
    else 0xfffffffful in
  pop_frame ();
  res


val box_open_detached_afternm:
    mlen:size_t
  -> m:lbuffer uint8 mlen
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint m c /\ disjoint tag m /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies (loc m) h0 h1 /\
    (let msg = Spec.box_open_detached_afternm (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq h1 m == Some?.v msg
    | _ -> None? msg))

[@CInline]
let box_open_detached_afternm mlen m k n c tag =
  secretbox_open_detached mlen m k n c tag


val box_open_detached:
    mlen:size_t
  -> m:lbuffer uint8 mlen
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint m c /\ disjoint tag m /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies (loc m) h0 h1 /\
    (let msg = Spec.box_open_detached (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 tag) (as_seq h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq h1 m == Some?.v msg
    | _ -> None? msg))

[@CInline]
let box_open_detached mlen m pk sk n c tag =
  push_frame();
  let k = create 32ul (u8 0) in
  let r = box_beforenm k pk sk in
  let res =
    if r =. size 0 then
      box_open_detached_afternm mlen m k n c tag
    else 0xfffffffful in
  pop_frame();
  res


val box_easy_afternm:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> c:lbuffer uint8 (mlen +! 16ul)
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies (loc c) h0 h1 /\
    as_seq h1 c == Spec.box_easy_afternm (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))

[@CInline]
let box_easy_afternm mlen c k n m =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  let res = box_detached_afternm mlen cip tag k n m in
  let h1 = ST.get () in
  FStar.Seq.Properties.lemma_split (as_seq h1 c) 16;
  res


val box_easy:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> c:lbuffer uint8 (mlen +! 16ul)
  -> sk:lbuffer uint8 32ul
  -> pk:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies (loc c) h0 h1 /\
    (let cipher = Spec.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m) in
    match r with
    | 0ul -> Some? cipher /\ as_seq h1 c == Some?.v cipher
    | _ -> None? cipher))

[@CInline]
let box_easy mlen c sk pk n m =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  let res = box_detached mlen cip tag sk pk n m in
  let h1 = ST.get () in
  FStar.Seq.Properties.lemma_split (as_seq h1 c) 16;
  res


val box_open_easy_afternm:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> m:lbuffer uint8 mlen
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 (mlen +! 16ul) ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures  fun h0 r h1 -> modifies (loc m) h0 h1 /\
   (let msg = Spec.box_open_easy_afternm (as_seq h0 k) (as_seq h0 n) (as_seq h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq h1 m == Some?.v msg
    | _ -> None? msg))

[@CInline]
let box_open_easy_afternm mlen m k n c =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  box_open_detached_afternm mlen m k n cip tag


val box_open_easy:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> m:lbuffer uint8 mlen
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 (mlen +! 16ul) ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures  fun h0 r h1 -> modifies (loc m) h0 h1 /\
   (let msg = Spec.box_open_easy (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq h1 m == Some?.v msg
    | _ -> None? msg))

[@CInline]
let box_open_easy mlen m pk sk n c =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  box_open_detached mlen m pk sk n cip tag
