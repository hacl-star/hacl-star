module Hacl.Impl.BignumQ.Mul

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence

open Hacl.Spec.BignumQ.Definitions

module ST = FStar.HyperStack.ST
module S = Spec.Ed25519

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let qelemB = lbuffer uint64 5ul

inline_for_extraction noextract
let qelem_wide = lbuffer uint64 10ul


noextract
let as_nat (h:mem) (e:qelemB) : GTot nat =
  let s = as_seq h e in
  as_nat5 (s.[0], s.[1], s.[2], s.[3], s.[4])


noextract
let wide_as_nat (h:mem) (e:qelem_wide) : GTot nat =
  let s = as_seq h e in
  wide_as_nat5 (s.[0], s.[1], s.[2], s.[3], s.[4], s.[5], s.[6], s.[7], s.[8], s.[9])


noextract
let qelem_fits (h:mem) (f:qelemB) (m:scale64_5) : Type0 =
  let s = as_seq h f in
  qelem_fits5 (s.[0], s.[1], s.[2], s.[3], s.[4]) m


noextract
let qelem_wide_fits (h:mem) (f:qelem_wide) (m:scale64_10) : Type0 =
  let s = as_seq h f in
  qelem_wide_fits5 (s.[0], s.[1], s.[2], s.[3], s.[4], s.[5], s.[6], s.[7], s.[8], s.[9]) m


val barrett_reduction:
    z:qelemB
  -> t:qelem_wide ->
  Stack unit
  (requires fun h -> live h z /\ live h t /\
    qelem_wide_fits h t (1, 1, 1, 1, 1, 1, 1, 1, 1, 1) /\
    wide_as_nat h t < pow2 512)
  (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1 /\
    qelem_fits h1 z (1, 1, 1, 1, 1) /\
    as_nat h1 z == wide_as_nat h0 t % S.q)

val mul_modq:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
  (requires fun h -> live h z /\ live h x /\ live h y /\
    qelem_fits h x (1, 1, 1, 1, 1) /\
    qelem_fits h y (1, 1, 1, 1, 1) /\
    as_nat h x < pow2 256 /\
    as_nat h y < pow2 256)
  (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1 /\
    qelem_fits h1 z (1, 1, 1, 1, 1) /\
    as_nat h1 z == (as_nat h0 x * as_nat h0 y) % S.q)

val add_modq:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
  (requires fun h -> live h z /\ live h x /\ live h y /\
    qelem_fits h x (1, 1, 1, 1, 1) /\
    qelem_fits h y (1, 1, 1, 1, 1) /\
    as_nat h x < S.q /\ as_nat h y < S.q)
  (ensures fun h0 _ h1 -> modifies (loc z) h0 h1 /\
    qelem_fits h1 z (1, 1, 1, 1, 1) /\
    as_nat h1 z == (as_nat h0 x + as_nat h0 y) % S.q)
