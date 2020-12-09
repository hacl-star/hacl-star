module Hacl.Impl.Poly.Field

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

include Hacl.Spec.Poly
open Hacl.Spec.Poly.Lemmas

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Spec.Poly

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction
let felem = lbuffer uint64 5ul
inline_for_extraction
let precomp_r = lbuffer uint64 10ul //[r; 5 * r]


let as_felem5 (h:mem) (f:felem) : GTot felem5 =
  to_felem5 (as_seq h f)

let felem_fits (h:mem) (f:felem) (m:scale32_5) : Type0 =
  felem_fits5 (as_felem5 h f) m

let as_nat (h:mem) (f:felem) : GTot nat =
  as_nat5 (as_felem5 h f)

let feval (h:mem) (f:felem) : GTot S.felem =
  feval5 (as_felem5 h f)


let precomp_r_pre (h:mem) (p:precomp_r) : Type0 =
  let r  = gsub p 0ul 5ul in
  let r5 = gsub p 5ul 5ul in
  felem_fits h r  (1, 1, 1, 1, 1) /\
  felem_fits h r5 (5, 5, 5, 5, 5) /\
  as_felem5 h r5 == precomp_r5 (as_felem5 h r)


inline_for_extraction
val mk_felem:
    b:lbuffer uint64 5ul
  -> s0:uint64 -> s1:uint64 -> s2:uint64 -> s3:uint64 -> s4:uint64 ->
  Stack unit
  (requires fun h -> live h b)
  (ensures  fun h0 _ h1 -> modifies (loc b) h0 h1 /\
    as_felem5 h1 b == (s0, s1, s2, s3, s4) /\
    as_nat h1 b == as_nat5 (s0, s1, s2, s3, s4))

let mk_felem b s0 s1 s2 s3 s4 =
  b.(0ul) <- s0;
  b.(1ul) <- s1;
  b.(2ul) <- s2;
  b.(3ul) <- s3;
  b.(4ul) <- s4


inline_for_extraction
val set_zero: f:felem ->
  Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    felem_fits h1 f (0, 0, 0, 0, 0) /\
    feval h1 f == 0)

let set_zero f =
  mk_felem f (u64 0) (u64 0) (u64 0) (u64 0) (u64 0)


inline_for_extraction
val precompute_r5: f1:felem -> f2:felem ->
  Stack unit
  (requires fun h ->
    live h f1 /\ live h f2 /\
    felem_fits h f2 (1, 1, 1, 1, 1))
  (ensures  fun h0 _ h1 -> modifies (loc f1) h0 h1 /\
    as_felem5 h1 f1 == precomp_r5 (as_felem5 h0 f2))

let precompute_r5 f1 f2 =
  let (a0, a1, a2, a3, a4) =
    precomp_r5 (f2.(0ul),f2.(1ul),f2.(2ul),f2.(3ul),f2.(4ul)) in
  mk_felem f1 a0 a1 a2 a3 a4


val fadd_mul_r: acc:felem -> f1:felem -> p:precomp_r ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h f1 /\ live h p /\
    felem_fits h acc (2, 2, 2, 2, 2) /\
    felem_fits h f1 (1, 1, 1, 1, 1) /\
    precomp_r_pre h p)
  (ensures  fun h0 _ h1 -> modifies (loc acc) h0 h1 /\
    felem_fits h1 acc (2, 2, 2, 2, 2) /\
    feval h1 acc == S.fmul (S.fadd (feval h0 acc) (feval h0 f1)) (feval h0 (gsub p 0ul 5ul)))

let fadd_mul_r acc f1 p =
  let r  = sub p 0ul 5ul in
  let r5 = sub p 5ul 5ul in
  let (a0, a1, a2, a3, a4) =
    add_mul_r5
      (acc.(0ul), acc.(1ul), acc.(2ul), acc.(3ul), acc.(4ul))
      (f1.(0ul), f1.(1ul), f1.(2ul), f1.(3ul), f1.(4ul))
      (r.(0ul), r.(1ul), r.(2ul), r.(3ul), r.(4ul))
      (r5.(0ul), r5.(1ul), r5.(2ul), r5.(3ul), r5.(4ul)) in
  mk_felem acc a0 a1 a2 a3 a4


(* The proofs of the following functions can be found in hacl-star/code/poly1305 *)
inline_for_extraction
val load_felem_le: f:felem -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h f /\ live h b)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    as_nat h1 f == BSeq.nat_from_bytes_le (as_seq h0 b))

let load_felem_le f b =
  let h0 = ST.get () in
  let lo = uint_from_bytes_le #U64 (sub b 0ul 8ul) in
  let hi = uint_from_bytes_le #U64 (sub b 8ul 8ul) in
  assume (v hi * pow2 64 + v lo == BSeq.nat_from_bytes_le (as_seq h0 b));
  let (f0, f1, f2, f3, f4) = load_felem5 lo hi in
  mk_felem f f0 f1 f2 f3 f4;
  let h1 = ST.get () in
  assume (felem_fits h1 f (1, 1, 1, 1, 1));
  assume (as_nat h1 f == v hi * pow2 64 + v lo)


inline_for_extraction
val set_bit128: f:felem ->
  Stack unit
  (requires fun h -> live h f /\
    felem_fits h f (1, 1, 1, 1, 1) /\
    as_nat h f < pow2 128)
  (ensures  fun h0 _ h1 -> modifies (loc f) h0 h1 /\
    felem_fits h1 f (1, 1, 1, 1, 1) /\
    as_nat h1 f == pow2 128 + as_nat h0 f)

let set_bit128 f =
  let h0 = ST.get () in
  let (a0, a1, a2, a3, a4) =
    set_bit128_5 (f.(0ul),f.(1ul),f.(2ul),f.(3ul),f.(4ul)) in
  mk_felem f a0 a1 a2 a3 a4;
  let h1 = ST.get () in
  assume (felem_fits h1 f (1, 1, 1, 1, 1));
  assume (as_nat h1 f == pow2 128 + as_nat h0 f)
