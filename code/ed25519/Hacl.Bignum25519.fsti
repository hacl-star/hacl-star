module Hacl.Bignum25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer

module S51 = Hacl.Spec.Curve25519.Field51.Definition
module S56 = Hacl.Spec.Ed25519.Field56.Definition
module F51 = Hacl.Impl.Ed25519.Field51
module F56 = Hacl.Impl.Ed25519.Field56

module SC = Spec.Curve25519

(* Type abbreviations *)
inline_for_extraction noextract
let felem = lbuffer uint64 5ul

(* A point is buffer of size 20, that is 4 consecutive buffers of size 5 *)
inline_for_extraction noextract
let point = lbuffer uint64 20ul

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let getx (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul 5ul /\ h0 == h1)
  = sub p 0ul 5ul
inline_for_extraction noextract
let gety (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 5ul 5ul /\ h0 == h1)
  = sub p 5ul 5ul
inline_for_extraction noextract
let getz (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 10ul 5ul /\ h0 == h1)
  = sub p 10ul 5ul
inline_for_extraction noextract
let gett (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 15ul 5ul /\ h0 == h1)
  = sub p 15ul 5ul

inline_for_extraction noextract
val make_u64_5:
    b:lbuffer uint64 5ul
  -> s0:uint64 -> s1:uint64 -> s2:uint64 -> s3:uint64 -> s4:uint64 ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      F51.as_felem h1 b == (s0, s1, s2, s3, s4) /\
      F51.as_nat h1 b == S51.as_nat5 (s0, s1, s2, s3, s4)
    )

inline_for_extraction noextract
val make_u64_10:
    b:lbuffer uint64 10ul
  -> s0:uint64 -> s1:uint64 -> s2:uint64 -> s3:uint64 -> s4:uint64
  -> s5:uint64 -> s6:uint64 -> s7:uint64 -> s8:uint64 -> s9:uint64 ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      (let s = as_seq h1 b in
       Seq.index s 0 == s0 /\
       Seq.index s 1 == s1 /\
       Seq.index s 2 == s2 /\
       Seq.index s 3 == s3 /\
       Seq.index s 4 == s4 /\
       Seq.index s 5 == s5 /\
       Seq.index s 6 == s6 /\
       Seq.index s 7 == s7 /\
       Seq.index s 8 == s8 /\
       Seq.index s 9 == s9)
    )

inline_for_extraction noextract
val make_u128_9:
    b:lbuffer uint128 9ul
  -> s0:uint128 -> s1:uint128 -> s2:uint128 -> s3:uint128 -> s4:uint128
  -> s5:uint128 -> s6:uint128 -> s7:uint128 -> s8:uint128 ->
  Stack unit
    (requires fun h -> live h b)
    (ensures fun h0 _ h1 -> modifies (loc b) h0 h1)

inline_for_extraction noextract
val make_zero:
  b:lbuffer uint64 5ul ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      F51.mul_inv_t h1 b /\
      F51.fevalh h1 b == SC.zero
    )

inline_for_extraction noextract
val make_one:
  b:lbuffer uint64 5ul ->
  Stack unit
    (requires fun h -> live h b)
    (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
      F51.mul_inv_t h1 b /\
      F51.fevalh h1 b == SC.one
    )

val fsum:
    a:felem
  -> b:felem ->
  Stack unit
    (requires fun h -> live h a /\ live h b /\ disjoint a b /\
      F51.felem_fits h a (1, 2, 1, 1, 1) /\
      F51.felem_fits h b (1, 2, 1, 1, 1)
    )
    (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
      F51.felem_fits h1 a (2, 4, 2, 2, 2) /\
      F51.fevalh h1 a == F51.fevalh h0 a `SC.fadd` F51.fevalh h0 b
    )

val fdifference:
    a:felem
  -> b:felem ->
  Stack unit
    (requires fun h -> live h a /\ live h b /\ disjoint a b /\
      F51.felem_fits h a (1, 2, 1, 1, 1) /\
      F51.felem_fits h b (1, 2, 1, 1, 1)
    )
    (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
      F51.felem_fits h1 a (9, 10, 9, 9, 9) /\
      F51.fevalh h1 a == F51.fevalh h0 b `SC.fsub` F51.fevalh h0 a
    )

val reduce_513:
  a:felem ->
  Stack unit
    (requires fun h -> live h a /\
      F51.felem_fits h a (9, 10, 9, 9, 9)
    )
    (ensures  fun h0 _ h1 -> modifies (loc a) h0 h1 /\
      F51.fevalh h1 a == F51.fevalh h0 a /\
      F51.mul_inv_t h1 a
    )


val fmul:
    out:felem
  -> a:felem
  -> b:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\ live h b /\
      F51.felem_fits h a (9, 10, 9, 9, 9) /\
      F51.felem_fits h b (9, 10, 9, 9, 9)
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.mul_inv_t h1 out /\
      F51.fevalh h1 out == SC.fmul (F51.fevalh h0 a) (F51.fevalh h0 b)
    )

val times_2:
    out:felem
  -> a:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\ F51.mul_inv_t h a)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.felem_fits h1 out (2, 4, 2, 2, 2) /\
      F51.fevalh h1 out == 2 `SC.fmul` F51.fevalh h0 a
    )

val times_d:
    out:felem
  -> a:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\
      F51.mul_inv_t h a
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.mul_inv_t h1 out /\
      F51.fevalh h1 out == Spec.Ed25519.d `SC.fmul` F51.fevalh h0 a
    )

val times_2d:
    out:felem
  -> a:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\
      F51.mul_inv_t h a
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.mul_inv_t h1 out /\
      F51.fevalh h1 out == 2 `SC.fmul` Spec.Ed25519.d `SC.fmul` F51.fevalh h0 a
    )

val fsquare:
    out:felem
  -> a:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\ disjoint a out /\
      F51.felem_fits h a (9, 10, 9, 9, 9)
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.mul_inv_t h1 out /\
      F51.fevalh h1 out == F51.fevalh h0 a `SC.fmul` F51.fevalh h0 a
    )

val fsquare_times:
    out:felem
  -> a:felem
  -> n:size_t{v n > 0} ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\ disjoint out a /\
      F51.felem_fits h a (1, 2, 1, 1, 1)
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.felem_fits h1 out (1, 2, 1, 1, 1) /\
      F51.fevalh h1 out == Hacl.Spec.Curve25519.Finv.pow (F51.fevalh h0 a) (pow2 (v n))
    )

val fsquare_times_inplace:
    out:felem
  -> n:size_t{v n > 0} ->
  Stack unit
    (requires fun h -> live h out /\ F51.felem_fits h out (1, 2, 1, 1, 1))
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.felem_fits h1 out (1, 2, 1, 1, 1) /\
      F51.fevalh h1 out == Hacl.Spec.Curve25519.Finv.pow (F51.fevalh h0 out) (pow2 (v n))
    )

val inverse:
    out:felem
  -> a:felem ->
  Stack unit
    (requires fun h -> live h out /\ live h a /\ disjoint a out /\
      F51.felem_fits h a (1, 2, 1, 1, 1)
    )
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.felem_fits h1 out (1, 2, 1, 1, 1) /\
      F51.fevalh h1 out == Spec.Ed25519.modp_inv (F51.fevalh h0 a)
    )

val reduce:
  out:felem ->
  Stack unit
    (requires fun h -> live h out /\ F51.mul_inv_t h out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      F51.felem_fits h1 out (1, 1, 1, 1, 1) /\
      F51.fevalh h0 out == F51.fevalh h1 out /\
      F51.fevalh h1 out == F51.as_nat h1 out
    )

val load_51:
    output:lbuffer uint64 5ul
  -> input:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h output /\ live h input)
    (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      F51.felem_fits h1 output (1, 1, 1, 1, 1) /\
      F51.as_nat h1 output == (nat_from_bytes_le (as_seq h0 input) % pow2 255)
    )

val store_51:
    output:lbuffer uint8 32ul
  -> input:lbuffer uint64 5ul ->
  Stack unit
    (requires fun h -> live h input /\ live h output /\ F51.mul_inv_t h input)
    (ensures fun h0 _ h1 -> modifies (loc output) h0 h1 /\
      as_seq h1 output == nat_to_bytes_le 32 (F51.fevalh h0 input)
    )
