module Hacl.Impl.Curve25519.Generic

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Fields
module S = Spec.Curve25519

inline_for_extraction noextract
let scalarmult_st (s:field_spec) =
    o:lbuffer uint8 32ul
  -> k:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 o /\ live h0 k /\ live h0 i /\
      disjoint o i /\ disjoint o k)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.scalarmult (as_seq h0 k) (as_seq h0 i))

inline_for_extraction noextract
let secret_to_public_st (s: field_spec) =
    o:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.secret_to_public (as_seq h0 i))

inline_for_extraction noextract
let ecdh_st (s:field_spec) =
    o:lbuffer uint8 32ul
  -> k:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack bool
    (requires fun h0 ->
      (s = M64 ==> Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)) /\
      live h0 o /\ live h0 k /\ live h0 i /\
      disjoint o i /\ disjoint o k)
    (ensures  fun h0 r h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.scalarmult (as_seq h0 k) (as_seq h0 i)
      /\ (not r == Lib.ByteSequence.lbytes_eq #32 (as_seq h1 o) (Lib.Sequence.create 32 (u8 0))))
