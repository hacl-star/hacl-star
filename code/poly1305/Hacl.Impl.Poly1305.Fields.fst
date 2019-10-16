module Hacl.Impl.Poly1305.Fields

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Poly1305.Field32xN_32
open Hacl.Impl.Poly1305.Field32xN_128
open Hacl.Impl.Poly1305.Field32xN_256
open Hacl.Impl.Poly1305.Field32xN

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.Poly1305
module Vec = Hacl.Spec.Poly1305.Vec
module F32xN = Hacl.Impl.Poly1305.Field32xN


#reset-options "--z3rlimit 50 --max_fuel 0 --max_fuel 0"

type field_spec =
  | M32
  | M128
  | M256

unfold noextract
let width (s:field_spec) : Vec.lanes =
  match s with
  | M32  -> 1
  | M128 -> 2
  | M256 -> 4

unfold noextract
let limb (s:field_spec) =
  match s with
  | M32  -> F32xN.uint64xN 1
  | M128 -> F32xN.uint64xN 2
  | M256 -> F32xN.uint64xN 4

unfold noextract
let limb_zero (s:field_spec) : limb s=
  match s with
  | M32  -> F32xN.zero 1
  | M128 -> F32xN.zero 2
  | M256 -> F32xN.zero 4

unfold noextract
let wide (s:field_spec) =
  match s with
  | M32  -> F32xN.uint64xN 1
  | M128 -> F32xN.uint64xN 2
  | M256 -> F32xN.uint64xN 4

unfold noextract
let nlimb (s:field_spec) : size_t =
  match s with
  | M32  -> 5ul
  | M128 -> 5ul
  | M256 -> 5ul

unfold noextract
let blocklen (s:field_spec) : r:size_t{0 < v r /\ v r == width s * S.size_block} =
  match s with
  | M32  -> 16ul
  | M128 -> 32ul
  | M256 -> 64ul

unfold noextract
let nelem (s:field_spec) : size_t =
  match s with
  | M32  -> 1ul
  | M128 -> 2ul
  | M256 -> 4ul

unfold noextract
let precomplen (s:field_spec) : size_t =
  match s with
  | M32  -> 20ul
  | M128 -> 20ul
  | M256 -> 20ul

inline_for_extraction noextract
type felem (s:field_spec) = lbuffer (limb s) (nlimb s)
type felem_wide (s:field_spec) = lbuffer (wide s) (nlimb s)
inline_for_extraction noextract
type precomp_r (s:field_spec) = lbuffer (limb s) (precomplen s)

noextract
val felem_fits: #s:field_spec -> h:mem -> f:felem s -> m:F32xN.scale32_5 -> Type0
let felem_fits #s h f m =
  match s with
  | M32  -> F32xN.felem_fits #1 h f m
  | M128 -> F32xN.felem_fits #2 h f m
  | M256 -> F32xN.felem_fits #4 h f m

noextract
val fas_nat: #s:field_spec -> h:mem -> e:felem s -> GTot (LSeq.lseq nat (width s))
let fas_nat #s h e =
  match s with
  | M32  -> F32xN.fas_nat #1 h e
  | M128 -> F32xN.fas_nat #2 h e
  | M256 -> F32xN.fas_nat #4 h e

noextract
val feval: #s:field_spec -> h:mem -> e:felem s -> GTot (LSeq.lseq S.felem (width s))
let feval #s h e =
  match s with
  | M32  -> F32xN.feval #1 h e
  | M128 -> F32xN.feval #2 h e
  | M256 -> F32xN.feval #4 h e

unfold noextract
let op_String_Access #a #len = LSeq.index #a #len

val lemma_feval_is_fas_nat: #s:field_spec -> h:mem -> f:felem s ->
  Lemma
  (requires F32xN.felem_less #(width s) h f (pow2 128))
  (ensures  (forall (i:nat). i < width s ==> (feval h f).[i] == (fas_nat h f).[i]))

let lemma_feval_is_fas_nat #s h f =
  F32xN.lemma_feval_is_fas_nat #(width s) h f

inline_for_extraction noextract
val create_felem: s:field_spec ->
  StackInline (felem s)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 5 (limb_zero s)) /\
    feval h1 f == LSeq.create (width s) 0)

let create_felem s =
  match s with
  | M32  -> (F32xN.create_felem 1) <: felem s
  | M128 -> (F32xN.create_felem 2) <: felem s
  | M256 -> (F32xN.create_felem 4) <: felem s


inline_for_extraction noextract
val load_felem_le:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h f /\ live h b)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    F32xN.felem_less #(width s) h1 f (pow2 128) /\
    feval h1 f == LSeq.create (width s) (BSeq.nat_from_bytes_le (as_seq h0 b)))

let load_felem_le #s f b =
  match s with
  | M32  -> F32xN.load_felem_le #1 f b
  | M128 -> F32xN.load_felem_le #2 f b
  | M256 -> F32xN.load_felem_le #4 f b


inline_for_extraction noextract
val load_felems_le:
    #s:field_spec
  -> f:felem s
  -> b:lbuffer uint8 (blocklen s) ->
  Stack unit
  (requires fun h -> live h f /\ live h b)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    F32xN.felem_less #(width s) h1 f (pow2 128) /\
    feval h1 f == Vec.load_elem #(width s) (as_seq h0 b))

let load_felems_le #s f b =
  match s with
  | M32  -> F32xN.load_felems_le #1 f b
  | M128 -> F32xN.load_felems_le #2 f b
  | M256 -> F32xN.load_felems_le #4 f b


inline_for_extraction noextract
val load_acc:
    #s:field_spec
  -> acc:felem s
  -> b:lbuffer uint8 (blocklen s) ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h b /\ disjoint acc b /\
    felem_fits h acc (1, 2, 1, 1, 1))
  (ensures  fun h0 _ h1 ->
    modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 3, 2, 2, 2) /\
    feval h1 acc == Vec.load_acc #(width s) (as_seq h0 b) (feval h0 acc).[0])

let load_acc #s acc b =
  match s with
  | M32 -> Field32xN_32.load_acc1 acc b
  | M128 -> Field32xN_128.load_acc2 acc b
  | M256 -> Field32xN_256.load_acc4 acc b


inline_for_extraction noextract
val set_bit:
    #s:field_spec
  -> f:felem s
  -> i:size_t{size_v i <= 128} ->
  Stack unit
  (requires fun h ->
    live h f /\
    felem_fits h f (1, 1, 1, 1, 1) /\
    F32xN.felem_less #(width s) h f (pow2 (v i)))
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    (Math.Lemmas.pow2_le_compat 128 (v i);
    feval h1 f == LSeq.map (Vec.pfadd (pow2 (v i))) (feval h0 f)))

let set_bit #s f i =
  match s with
  | M32  -> F32xN.set_bit #1 f i
  | M128 -> F32xN.set_bit #2 f i
  | M256 -> F32xN.set_bit #4 f i


inline_for_extraction noextract
val set_bit128:
    #s:field_spec
  -> f:felem s ->
  Stack unit
  (requires fun h ->
    live h f /\
    felem_fits h f (1, 1, 1, 1, 1) /\
    F32xN.felem_less #(width s) h f (pow2 128))
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    feval h1 f == LSeq.map (Vec.pfadd (pow2 128)) (feval h0 f))

let set_bit128 #s f =
  match s with
  | M32  -> F32xN.set_bit128 #1 f
  | M128 -> F32xN.set_bit128 #2 f
  | M256 -> F32xN.set_bit128 #4 f


inline_for_extraction noextract
val set_zero:
    #s:field_spec
  -> f:felem s ->
  Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (0, 0, 0, 0, 0) /\
    feval h1 f == LSeq.create (width s) 0)

let set_zero #s f =
  match s with
  | M32  -> F32xN.set_zero #1 f
  | M128 -> F32xN.set_zero #2 f
  | M256 -> F32xN.set_zero #4 f


inline_for_extraction noextract
val reduce_felem:
    #s:field_spec
  -> f:felem s ->
  Stack unit
  (requires fun h ->
    live h f /\ F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h f))
  (ensures  fun h0 _ h1 ->
    modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    (fas_nat h1 f).[0] == (feval h0 f).[0])

let reduce_felem #s f =
  match s with
  | M32  -> F32xN.reduce_felem #1 f
  | M128 -> F32xN.reduce_felem #2 f
  | M256 -> F32xN.reduce_felem #4 f


inline_for_extraction noextract
val load_precompute_r:
    #s:field_spec
  -> p:precomp_r s
  -> r0:uint64
  -> r1:uint64 ->
  Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 ->
    modifies (loc p) h0 h1 /\
    F32xN.load_precompute_r_post #(width s) h1 p /\
    (assert (uint_v r1 * pow2 64 + uint_v r0 < pow2 128);
    feval h1 (gsub p 0ul 5ul) ==
      LSeq.create (width s) (uint_v r1 * pow2 64 + uint_v r0)))

let load_precompute_r #s p r0 r1 =
  match s with
  | M32  -> F32xN.load_precompute_r #1 p r0 r1
  | M128 -> F32xN.load_precompute_r #2 p r0 r1
  | M256 -> F32xN.load_precompute_r #4 p r0 r1


inline_for_extraction noextract
val fadd_mul_r:
    #s:field_spec
  -> out:felem s
  -> f1:felem s
  -> precomp:precomp_r s ->
  Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h precomp /\
    F32xN.fmul_precomp_r_pre #(width s) h precomp /\
    felem_fits h out (1, 2, 1, 1, 1) /\
    felem_fits h f1 (1, 1, 1, 1, 1))
  (ensures  fun h0 _ h1 ->
    modifies (loc out) h0 h1 /\
    F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 out) /\
    feval h1 out ==
    Vec.fmul (Vec.fadd (feval h0 out) (feval h0 f1)) (feval h0 (gsub precomp 0ul 5ul)))

let fadd_mul_r #s out f1 precomp =
  match s with
  | M32  -> F32xN.fadd_mul_r #1 out f1 precomp
  | M128 -> F32xN.fadd_mul_r #2 out f1 precomp
  | M256 -> F32xN.fadd_mul_r #4 out f1 precomp


inline_for_extraction noextract
val fmul_rn:
    #s:field_spec
  -> out:felem s
  -> f1:felem s
  -> precomp:precomp_r s ->
  Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h precomp /\
    (let rn = gsub precomp 10ul 5ul in
    let rn_5 = gsub precomp 15ul 5ul in
    felem_fits h f1 (2,3,2,2,2) /\
    felem_fits h rn (1,2,1,1,1) /\
    felem_fits h rn_5 (5,10,5,5,5) /\
    F32xN.as_tup5 #(width s) h rn_5 == F32xN.precomp_r5 (F32xN.as_tup5 h rn)))
  (ensures fun h0 _ h1 ->
    modifies (loc out) h0 h1 /\
    F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 out) /\
    feval h1 out == Vec.fmul (feval h0 f1) (feval h0 (gsub precomp 10ul 5ul)))

let fmul_rn #s out f1 precomp =
  match s with
  | M32  -> F32xN.fmul_rn #1 out f1 precomp
  | M128 -> F32xN.fmul_rn #2 out f1 precomp
  | M256 -> F32xN.fmul_rn #4 out f1 precomp


inline_for_extraction noextract
val fmul_rn_normalize:
    #s:field_spec
  -> out:felem s
  -> precomp:precomp_r s ->
  Stack unit
  (requires fun h ->
    live h out /\ live h precomp /\
    felem_fits h out (2,3,2,2,2) /\
    F32xN.load_precompute_r_post #(width s) h precomp)
  (ensures fun h0 _ h1 ->
    modifies (loc out) h0 h1 /\
    F32xN.acc_inv_t #(width s) (F32xN.as_tup5 h1 out) /\
    (feval h1 out).[0] ==
    Vec.normalize_n #(width s) (feval h0 (gsub precomp 0ul 5ul)).[0] (feval h0 out))

let fmul_rn_normalize #s out precomp =
  match s with
  | M32  -> Field32xN_32.fmul_r1_normalize out precomp
  | M128 -> Field32xN_128.fmul_r2_normalize out precomp
  | M256 -> Field32xN_256.fmul_r4_normalize out precomp

inline_for_extraction noextract
val fadd:
    #s:field_spec
  -> out:felem s
  -> f1:felem s
  -> f2:felem s ->
  Stack unit
  (requires fun h ->
    live h out /\ live h f1 /\ live h f2 /\
    felem_fits h f1 (1,2,1,1,1) /\
    felem_fits h f2 (1,1,1,1,1))
  (ensures fun h0 _ h1 ->
    modifies (loc out) h0 h1 /\
    felem_fits h1 out (2,3,2,2,2) /\
    feval h1 out == Vec.fadd (feval h0 f1) (feval h0 f2))

let fadd #s out f1 f2 =
  match s with
  | M32  -> F32xN.fadd #1 out f1 f2
  | M128 -> F32xN.fadd #2 out f1 f2
  | M256 -> F32xN.fadd #4 out f1 f2


inline_for_extraction noextract
val uints64_from_felem_le:
    #s:field_spec
  -> f:felem s ->
  Stack (uint64 & uint64)
  (requires fun h ->
    live h f /\ felem_fits h f (1, 1, 1, 1, 1))
  (ensures  fun h0 (lo, hi) h1 -> h0 == h1 /\
    v hi * pow2 64 + v lo == (fas_nat h0 f).[0] % pow2 128)

let uints64_from_felem_le #s f =
  match s with
  | M32  -> F32xN.uints64_from_felem_le #1 f
  | M128 -> F32xN.uints64_from_felem_le #2 f
  | M256 -> F32xN.uints64_from_felem_le #4 f


inline_for_extraction noextract
val uints64_from_bytes_le: b:lbuffer uint8 16ul ->
  Stack (uint64 & uint64)
  (requires fun h -> live h b)
  (ensures  fun h0 (lo, hi) h1 -> h0 == h1 /\
    v hi * pow2 64 + v lo == BSeq.nat_from_bytes_le (as_seq h0 b))

let uints64_from_bytes_le b =
  F32xN.uints64_from_bytes_le b


inline_for_extraction noextract
val uints64_to_bytes_le:
    b:lbuffer uint8 16ul
  -> lo:uint64
  -> hi:uint64 ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 ->
    modifies (loc b) h0 h1 /\
    as_seq h1 b == BSeq.nat_to_bytes_le 16 (v hi * pow2 64 + v lo))

let uints64_to_bytes_le b lo hi =
  F32xN.uints64_to_bytes_le b lo hi


inline_for_extraction noextract
val mod_add128:
    a:(uint64 & uint64)
  -> b:(uint64 & uint64) ->
  Pure (uint64 & uint64)
  (requires True)
  (ensures (fun (r0, r1) ->
    let (a0, a1) = a in let (b0, b1) = b in
    v r1 * pow2 64 + v r0 == ((v a1 + v b1) * pow2 64 + v a0 + v b0) % pow2 128))

let mod_add128 a b =
  F32xN.mod_add128 a b
