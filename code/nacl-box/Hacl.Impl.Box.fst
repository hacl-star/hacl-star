module Hacl.Impl.Box

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.SecretBox

module Spec = Spec.Box
module LSeq = Lib.Sequence

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val box_init:
    k:lbytebuf 32ul
  -> pk:lbytebuf 32ul
  -> sk:lbytebuf 32ul ->
  Stack unit
  (requires fun h -> live h k /\ live h pk /\ live h sk /\
    disjoint k pk /\ disjoint k sk)
  (ensures  fun h0 _ h1 -> modifies (loc k) h0 h1 /\
    as_seq h1 k == Spec.box_init (as_seq h0 pk) (as_seq h0 sk))
let box_init k pk sk =
  push_frame();
  let n0 = create 16ul (u8 0) in
  Hacl.Curve25519_51.ecdh k sk pk;
  Hacl.Salsa20.hsalsa20 k k n0;
  pop_frame()

#set-options "--z3rlimit 100"

val box_detached:
    mlen:size_t
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul
  -> sk:lbytebuf 32ul
  -> pk:lbytebuf 32ul
  -> n:lbytebuf 24ul
  -> m:lbuffer uint8 mlen ->
  Stack unit
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\ live h tag /\
    disjoint tag c /\ disjoint tag m /\ eq_or_disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc c |+| loc tag) h0 h1 /\
    (as_seq h1 tag, as_seq h1 c) == Spec.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m))
let box_detached mlen c tag sk pk n m =
  let h0 = ST.get () in
  push_frame();
  let k = create 32ul (u8 0) in
  box_init k pk sk;
  let h1 = ST.get () in
  secretbox_detached mlen c tag k n m;
  let h2 = ST.get () in
  assert (
    let (tag1, c1) = Spec.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m) in
    (as_seq h2 tag, as_seq h2 c) == (tag1, c1));
  pop_frame()

val box_open_detached:
    mlen:size_t
  -> m:lbuffer uint8 mlen
  -> pk:lbytebuf 32ul
  -> sk:lbytebuf 32ul
  -> n:lbytebuf 24ul
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
let box_open_detached mlen m pk sk n c tag =
  push_frame();
  let k = create 32ul (u8 0) in
  box_init k pk sk;
  let res = secretbox_open_detached mlen m k n c tag in
  pop_frame();
  res

val box_easy:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> c:lbuffer uint8 (mlen +! 16ul)
  -> sk:lbytebuf 32ul
  -> pk:lbytebuf 32ul
  -> n:lbytebuf 24ul
  -> m:lbuffer uint8 mlen ->
  Stack unit
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc c) h0 h1 /\
    as_seq h1 c == Spec.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq h0 m))
let box_easy mlen c sk pk n m =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  box_detached mlen cip tag sk pk n m;
  let h1 = ST.get () in
  FStar.Seq.Properties.lemma_split (as_seq h1 c) 16

val box_open_easy:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> m:lbuffer uint8 mlen
  -> pk:lbytebuf 32ul
  -> sk:lbytebuf 32ul
  -> n:lbytebuf 24ul
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
let box_open_easy mlen m pk sk n c =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  box_open_detached mlen m pk sk n cip tag
