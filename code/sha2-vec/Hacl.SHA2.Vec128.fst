module Hacl.SHA2.Vec128

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
module Spec = Spec.Agile.Hash
module SpecVec = Hacl.Spec.SHA2.Vec


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
private
val sha256_update4: update_vec_t SHA2_256 M128
let sha256_update4 b hash = update #SHA2_256 #M128 b hash


val sha256_4 (r0 r1 r2 r3: lbuffer uint8 32ul) (len:size_t) (b0 b1 b2 b3: lbuffer uint8 len) :
  Stack unit
  (requires fun h0 -> v len <= max_input_length SHA2_256 /\
    live4 h0 b0 b1 b2 b3 /\ live4 h0 r0 r1 r2 r3 /\ internally_disjoint4 r0 r1 r2 r3)
  (ensures  fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3) h0 h1 /\
    as_seq h1 r0 == Spec.hash SHA2_256 (as_seq h0 b0) /\
    as_seq h1 r1 == Spec.hash SHA2_256 (as_seq h0 b1) /\
    as_seq h1 r2 == Spec.hash SHA2_256 (as_seq h0 b2) /\
    as_seq h1 r3 == Spec.hash SHA2_256 (as_seq h0 b3))

let sha256_4 r0 r1 r2 r3 len b0 b1 b2 b3 =
  let h0 = ST.get() in
  let ib = ntup4 (b0,(b1,(b2,b3))) in
  let rb = ntup4 (r0,(r1,(r2,r3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  loc_multi4 rb;
  hash #SHA2_256 #M128 sha256_update4 rb len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_256 #M128 (v len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 r0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 r1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 r2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 r3)
