module Hacl.Impl.SHA2.Core
open FStar.Mul
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.IntVector
open Lib.MultiBuffer
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
module Spec = Hacl.Spec.SHA2

val sha256: hash:lbuffer uint8 32ul -> len:size_t -> b:lbuffer uint8 len ->
    Stack unit
    (requires (fun h0 -> live h0 b /\ live h0 hash /\ disjoint hash b))
    (ensures (fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
                           as_seq h1 hash == Spec.hash #SHA2_256 (v len) (as_seq h0 b)))


val sha256_4 (r0 r1 r2 r3: lbuffer uint8 32ul)
             (len:size_t)
             (b0 b1 b2 b3: lbuffer uint8 len) :
    Stack unit
    (requires (fun h0 -> live4 h0 b0 b1 b2 b3 /\
                       live4 h0 r0 r1 r2 r3 /\
                       internally_disjoint4 r0 r1 r2 r3))
    (ensures (fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3) h0 h1 /\
                           as_seq h1 r0 == Spec.hash #SHA2_256 (v len) (as_seq h0 b0) /\
                           as_seq h1 r1 == Spec.hash #SHA2_256 (v len) (as_seq h0 b1) /\
                           as_seq h1 r2 == Spec.hash #SHA2_256 (v len) (as_seq h0 b2) /\
                           as_seq h1 r3 == Spec.hash #SHA2_256 (v len) (as_seq h0 b3)))



val sha256_8 (r0 r1 r2 r3 r4 r5 r6 r7 : lbuffer uint8 32ul)
             (len:size_t)
             (b0 b1 b2 b3 b4 b5 b6 b7 : lbuffer uint8 len) :
    Stack unit
    (requires (fun h0 -> live8 h0 b0 b1 b2 b3 b4 b5 b6 b7 /\ live8 h0 r0 r1 r2 r3 r4 r5 r6 r7 /\
                       internally_disjoint8 r0 r1 r2 r3 r4 r5 r6 r7))
    (ensures (fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3 |+| loc r4 |+| loc r5 |+| loc r6 |+| loc r7) h0 h1 /\
                           as_seq h1 r0 == Spec.hash #SHA2_256 (v len) (as_seq h0 b0) /\
                           as_seq h1 r1 == Spec.hash #SHA2_256 (v len) (as_seq h0 b1) /\
                           as_seq h1 r2 == Spec.hash #SHA2_256 (v len) (as_seq h0 b2) /\
                           as_seq h1 r3 == Spec.hash #SHA2_256 (v len) (as_seq h0 b3) /\
                           as_seq h1 r4 == Spec.hash #SHA2_256 (v len) (as_seq h0 b4) /\
                           as_seq h1 r5 == Spec.hash #SHA2_256 (v len) (as_seq h0 b5) /\
                           as_seq h1 r6 == Spec.hash #SHA2_256 (v len) (as_seq h0 b6) /\
                           as_seq h1 r7 == Spec.hash #SHA2_256 (v len) (as_seq h0 b7)))

