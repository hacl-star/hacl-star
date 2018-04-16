module Spec.GaloisField

open FStar.Seq
open FStar.BitVector
open Spec.Lib.IntSeq
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes

(* We represent GF(2^n) with irreducible polynomial x^n + p(x), deg(p) <= n-1
   by GF n bv where bv is the big-endian bitvector for p(x)   *)
type polynomial (degree:nat) = bv_t (degree + 1)
type field' = | GF: bits:pos -> irred: polynomial (bits - 1) -> field'
let field = field'

let numbits (f:field) = f.bits
let mk_field bits irred = GF bits (UInt.to_vec #bits irred)

type felem (f:field) = bv_t f.bits

let to_felem #f u = UInt.to_vec #f.bits u
let from_felem #f (e:felem f) = UInt.from_vec #f.bits e
let zero #f : felem f = zero_vec #f.bits
let one #f : felem f = elem_vec #f.bits 0

let fadd (#f:field) (a:felem f) (b:felem f) : felem f = logxor_vec #f.bits a b
let op_Plus_At #f e1 e2 = fadd #f e1 e2

(* Properties *)

let add_comm (#f:field) (a:felem f) (b:felem f) = lemma_eq_intro (a +@ b) (b +@ a)

let add_asso (#f:field) (a:felem f) (b:felem f) (c:felem f) = lemma_eq_intro (a +@ b +@ c) (a +@ (b +@ c))

let add_zero (#f:field) (a:felem f) = lemma_eq_intro (a +@ zero) a

let shift_reduce (#f:field) (a:felem f) =
    if (Seq.index a (f.bits-1) = true) then
       fadd (shift_right_vec a 1) f.irred
    else (shift_right_vec a 1)

let cond_fadd (#f:field) (a:felem f) (b:felem f) (c:felem f) (n:nat{n < f.bits}) =
    if (Seq.index b n = true) then fadd c a else c

val cond_fadd_lemma: #f:field -> a:felem f -> b:felem f -> c:felem f -> d:felem f -> n:nat{n < f.bits} -> Lemma
  (requires True)
  (ensures cond_fadd a b c n `fadd` d = c `fadd` cond_fadd a b d n)
let cond_fadd_lemma #f a b c d n =
    if (Seq.index b n = true) then begin
       add_comm #f d a;
       add_asso #f c a d
    end else ()


let rec fmul_loop (#f:field) (a:felem f) (b:felem f) (n:nat{n<=f.bits})
    : Tot (felem f) (decreases (f.bits - n)) =
    if n = f.bits then zero #f
    else
       let n_1 : nat = n + 1 in
       let fmul_n_1 = fmul_loop (shift_reduce #f a)
       	   	      		b n_1 in
       cond_fadd a b fmul_n_1 n

let fmul (#f:field) (a:felem f) (b:felem f) = fmul_loop a b 0
let op_Star_At #f e1 e2 = fmul #f e1 e2

let carry_less_mul (#f:field) (a:bv_t 64) (b:bv_t 64) : Tot (uint128) =
  let b_nat:uint128 = u128 (UInt.from_vec b) in
  let c = repeat_range 0 64 (fun i c_i ->
    if (Seq.index a (63-i)) then
      c_i ^. (shift_left #U128 b_nat (u32 i))
    else
      c_i
  ) (u128 0) in
  c

(* Galoi field multiplication as implemented with intel intrinsics (only GF128!) *)
val fmul_intel_:
  #f:field{f.bits = 128 /\ f.irred = (UInt.to_vec #128 0xe1000000000000000000000000000000)} ->
  a:felem f ->
  b:felem f ->
  Tot (felem f)
let fmul_intel_ #f a b =
  // Ci = in ^ x, compute x = Ci * h
  let c_:uint128 = carry_less_mul #f (Seq.slice a 64 128) (Seq.slice b 64 128) in // _mm_clmulepi64_si128(Ci, h, 0x00)
  let d_:uint128 = carry_less_mul #f (Seq.slice a 0 64) (Seq.slice b 0 64) in // _mm_clmulepi64_si128(Ci, h, 0x11)
  let e_:uint128 = carry_less_mul #f (Seq.slice a 64 128) (Seq.slice b 0 64) in // _mm_clmulepi64_si128(Ci, h, 0x01)
  let f_:uint128 = carry_less_mul #f (Seq.slice a 0 64) (Seq.slice b 64 128) in // _mm_clmulepi64_si128(Ci, h, 0x10)
  let tmp = logxor #U128 e_ f_ in // _mm_xor_si128(e_, f_)
  let high_mask = u128 0xFFFFFFFFFFFFFFFF0000000000000000 in
  let z_high = tmp ^. (d_ <<. (u32 64)) in // _mm_xor_si128(tmp, _mm_slli_si128(d_, 8))
  let z_high = (d_ &. high_mask) |. ((z_high &. high_mask) >>. (u32 64)) in // _mm_unpackhi_epi64(z_high, d_)
  let z_low = (tmp <<. (u32 64)) ^. c_ in // _mm_xor_si128(_mm_slli_si128(tmp, 8), c_)
  let z_low = (z_low &. high_mask) |. (((c_ <<. (u32 64)) &. high_mask) >>. (u32 64)) in // _mm_unpackhi_epi64(_mm_slli_si128(c_, 8), z_low)

  // *x (left shift by one)
  let c_ = z_low <<. (u32 64) in // _mm_slli_si128(z_low, 8)
  let e_ = c_ >>. (u32 63) in // _mm_srli_epi64(c_, 63)
  let d_ = z_high <<. (u32 64) in // _mm_slli_si128(z_high, 8)
  let f_ = d_ >>. (u32 63) in // _mm_srli_epi64(d_, 63)
  let c_ = z_low >>. (u32 64) in // _mm_srli_si128(z_low, 8)
  let d_ = c_ >>. (u32 63) in // _mm_srli_epi64(c_, 63)
  let z_low = (z_low <<. (u32 1)) |. (e_) in // _mm_or_si128(_mm_slli_epi64(z_low, 1), e_)
  let z_high = ((z_high <<. (u32 1)) |. (f_)) |. (d_) in // _mm_or_si128(_mm_or_si128(_mm_slli_epi64(z_high, 1), f_), d_)

  // reduce
  let c_ = z_low <<. (u32 64) in // _mm_slli_si128(z_low, 8)
  let d_ = c_ <<. (u32 63) in // _mm_slli_epi64(c_, 63)
  let e_ = c_ <<. (u32 62) in // _mm_slli_epi64(c_, 62)
  let f_ = c_ <<. (u32 57) in //_mm_slli_epi64(c_, 57)
  let z_low = z_low ^. d_ ^. e_ ^. f_ in // _mm_xor_si128(_mm_xor_si128(_mm_xor_si128(z_low, d_), e_), f_)
  let c_ = z_low >>. (u32 64) in // _mm_srli_si128(z_low, 8)
  let d_ = c_ <<. (u32 63) in // _mm_slli_epi64(c_, 63)
  let d_ = (z_low >>. (u32 1)) |. d_ in // _mm_or_si128(_mm_srli_epi64(z_low, 1), d_)
  let e_ = c_ <<. (u32 62) in // _mm_slli_epi64(c_, 62)
  let e_ = (z_low >>. (u32 2)) |. e_ in // _mm_or_si128(_mm_srli_epi64(z_low, 2), e_)
  let f_ = c_ <<. (u32 57) in // _mm_slli_epi64(c_, 57)
  let f_ = (z_low >>. (u32 7)) |. f_ in // _mm_or_si128(_mm_srli_epi64(z_low, 7), f_)

  // _mm_xor_si128(_mm_xor_si128(_mm_xor_si128(_mm_xor_si128(z_high, z_low), d_), e_), f_)
  let x = z_high ^. z_low ^. d_ ^. e_ ^. f_ in
  to_felem #f (uint_to_nat #U128 x)

let fmul_intel
  (#f:field{f.bits = 128 /\ f.irred = (UInt.to_vec #128 0xe1000000000000000000000000000000)})
  (a:felem f)
  (b:felem f) =
  fmul_intel_ #f a b

val degree_: #f:field -> a:felem f -> i:nat{i < f.bits} -> Tot nat (decreases i)
let rec degree_ (#f:field) (a:felem f) (i:nat{i < f.bits}) =
  if i = 0 then 0
  else if Seq.index a (f.bits - i - 1) then i
  else degree_ #f a (i-1)

let degree #f a = degree_ #f a (f.bits - 1)

(* val finv_: #f:field -> s:felem f -> r:felem f -> v:felem f -> u:felem f -> Tot (felem f) (decreases (degree r + degree s))
let rec finv_ (#f:field) (s:felem f) (r:felem f) (v:felem f) (u:felem f) =
  let dr = degree r in
  let ds = degree s in
  if dr = 0 then u else
  if ds >= dr then
    let s' : felem f = fadd s (shift_left_vec r (ds - dr)) in
    let v' : felem f = fadd v (shift_left_vec u (ds - dr)) in
    finv_ #f s' r  v' u
  else
    let r' = s in
    let s' = r in
    let v' = u in
    let u' = v in
    let s' = fadd s' (shift_left_vec r' (dr - ds)) in
    let v' = fadd v' (shift_left_vec u' (dr - ds)) in
    finv_ #f s' r' v' u'

let finv (#f:field) (irr: felem f) (a:felem f) =
  if from_felem #f a = 0 then zero else
  let r = a in
  let s = irr in
  let dr = degree r in
  let ds = f.bits in
  let v = zero in
  let u = to_felem #f 1 in
  if dr = 0 then u else
    (* TODO: ds-dr doesn't type check *)
    let s' = fadd s (shift_left_vec r (ds - dr)) in
    let v' = fadd v (shift_left_vec u (ds - dr)) in
    finv_ #f s' r  v' u *)

val fexp: #f:field -> a:felem f -> n:nat{n >= 1} -> Tot (felem f) (decreases n)
let rec fexp #f a x =
  if x = 1 then a else
  if x = 2 then fmul #f a a else
  let r = fexp #f a (x / 2) in
  let r' = fmul #f r r in
  if (x % 2) = 0  then r'
  else fmul #f a r'
