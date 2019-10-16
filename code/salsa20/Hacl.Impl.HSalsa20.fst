module Hacl.Impl.HSalsa20

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Salsa20.Core32

module ST = FStar.HyperStack.ST
module Spec = Spec.Salsa20
module Loop = Lib.LoopCombinators
module Salsa20 = Hacl.Impl.Salsa20


#set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

inline_for_extraction
val hsalsa20_init:
    ctx:state
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h k /\ live h n /\
    disjoint ctx k /\ disjoint ctx n /\
    as_seq h ctx == Lib.Sequence.create 16 (u32 0))
  (ensures  fun h0 _ h1 -> modifies (loc ctx) h0 h1 /\
    as_seq h1 ctx == Spec.hsalsa20_init (as_seq h0 k) (as_seq h0 n))

let hsalsa20_init ctx k n =
  let h0 = ST.get() in
  push_frame();
  let k32 = create 8ul (u32 0) in
  let n32 = create 4ul (u32 0) in
  let h0' = ST.get() in
  uints_from_bytes_le k32 k;
  uints_from_bytes_le n32 n;
  let k0 = sub k32 0ul 4ul in
  let k1 = sub k32 4ul 4ul in
  ctx.(0ul) <- Spec.constant0;
  update_sub #MUT ctx 1ul 4ul k0;
  ctx.(5ul) <- Spec.constant1;
  update_sub #MUT ctx 6ul 4ul n32;
  ctx.(10ul) <- Spec.constant2;
  update_sub #MUT ctx 11ul 4ul k1;
  ctx.(15ul) <- Spec.constant3;
  let h1' = ST.get() in
  assert (modifies (loc ctx |+| loc k32 |+| loc n32) h0' h1');
  pop_frame();
  let h1 = ST.get() in
  assert (modifies (loc ctx) h0 h1)


val hsalsa20:
    out:lbuffer uint8 32ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.hsalsa20 (as_seq h0 key) (as_seq h0 n))

[@ CInline ]
let hsalsa20 out key n =
  push_frame();
  let ctx = create 16ul (u32 0) in
  hsalsa20_init ctx key n;
  Salsa20.rounds ctx;
  let r0 = ctx.(0ul) in
  let r1 = ctx.(5ul) in
  let r2 = ctx.(10ul) in
  let r3 = ctx.(15ul) in
  let r4 = ctx.(6ul) in
  let r5 = ctx.(7ul) in
  let r6 = ctx.(8ul) in
  let r7 = ctx.(9ul) in
  [@inline_let]
  let res_l = [r0;r1;r2;r3;r4;r5;r6;r7] in
  assert_norm (List.Tot.length res_l == 8);
  let res = createL res_l in
  uints_to_bytes_le #U32 8ul out res;
  pop_frame()
