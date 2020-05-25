module Hacl.SHA2.Vec256

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Spec.SHA2.Vec
open Hacl.Impl.SHA2.Generic

module ST = FStar.HyperStack.ST
module Spec = Hacl.Spec.SHA2
module SpecVec = Hacl.Spec.SHA2.Vec


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
private
val sha256_update8: update_vec_t SHA2_256 M256
let sha256_update8 b hash = update #SHA2_256 #M256 b hash


val sha256_8 (r0 r1 r2 r3 r4 r5 r6 r7 : lbuffer uint8 32ul) (len:size_t) (b0 b1 b2 b3 b4 b5 b6 b7 : lbuffer uint8 len) :
  Stack unit
  (requires fun h0 -> live8 h0 b0 b1 b2 b3 b4 b5 b6 b7 /\ live8 h0 r0 r1 r2 r3 r4 r5 r6 r7 /\ internally_disjoint8 r0 r1 r2 r3 r4 r5 r6 r7)
  (ensures  fun h0 _ h1 -> modifies (loc r0 |+| (loc r1 |+| (loc r2 |+| (loc r3 |+| (loc r4 |+| (loc r5 |+| (loc r6 |+| loc r7))))))) h0 h1 /\
    as_seq h1 r0 == Spec.hash #SHA2_256 (v len) (as_seq h0 b0) /\
    as_seq h1 r1 == Spec.hash #SHA2_256 (v len) (as_seq h0 b1) /\
    as_seq h1 r2 == Spec.hash #SHA2_256 (v len) (as_seq h0 b2) /\
    as_seq h1 r3 == Spec.hash #SHA2_256 (v len) (as_seq h0 b3) /\
    as_seq h1 r4 == Spec.hash #SHA2_256 (v len) (as_seq h0 b4) /\
    as_seq h1 r5 == Spec.hash #SHA2_256 (v len) (as_seq h0 b5) /\
    as_seq h1 r6 == Spec.hash #SHA2_256 (v len) (as_seq h0 b6) /\
    as_seq h1 r7 == Spec.hash #SHA2_256 (v len) (as_seq h0 b7))

let sha256_8 r0 r1 r2 r3 r4 r5 r6 r7 len b0 b1 b2 b3 b4 b5 b6 b7 =
  let h0 = ST.get() in
  let ib = ntup8 (b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))) in
  let rb = ntup8 (r0,(r1,(r2,(r3,(r4,(r5,(r6,r7))))))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  loc_multi8 rb;
  hash #SHA2_256 #M256 sha256_update8 rb len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_lemma #SHA2_256 #M256 (v len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 r0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 r1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 r2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 r3);
  assert ((as_seq_multi h1 rb).(|4|) == as_seq h1 r4);
  assert ((as_seq_multi h1 rb).(|5|) == as_seq h1 r5);
  assert ((as_seq_multi h1 rb).(|6|) == as_seq h1 r6);
  assert ((as_seq_multi h1 rb).(|7|) == as_seq h1 r7)


[@CInline]
private
val sha512_update4: update_vec_t SHA2_512 M256
let sha512_update4 b hash = update #SHA2_512 #M256 b hash


val sha512_4 (r0 r1 r2 r3 : lbuffer uint8 64ul) (len:size_t) (b0 b1 b2 b3 : lbuffer uint8 len) :
  Stack unit
  (requires fun h0 -> live4 h0 b0 b1 b2 b3 /\ live4 h0 r0 r1 r2 r3 /\ internally_disjoint4 r0 r1 r2 r3)
  (ensures  fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3) h0 h1 /\
    as_seq h1 r0 == Spec.hash #SHA2_512 (v len) (as_seq h0 b0) /\
    as_seq h1 r1 == Spec.hash #SHA2_512 (v len) (as_seq h0 b1) /\
    as_seq h1 r2 == Spec.hash #SHA2_512 (v len) (as_seq h0 b2) /\
    as_seq h1 r3 == Spec.hash #SHA2_512 (v len) (as_seq h0 b3))

let sha512_4 r0 r1 r2 r3 len b0 b1 b2 b3 =
  let h0 = ST.get() in
  let ib = ntup4 (b0,(b1,(b2,b3))) in
  let rb = ntup4 (r0,(r1,(r2,r3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  loc_multi4 rb;
  hash #SHA2_512 #M256 sha512_update4 rb len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_lemma #SHA2_512 #M256 (v len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 r0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 r1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 r2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 r3)
