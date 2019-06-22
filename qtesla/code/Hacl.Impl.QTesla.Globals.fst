module Hacl.Impl.QTesla.Globals

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Lemmas

module UI32 = FStar.UInt32
module UI64 = FStar.UInt64
module I64 = FStar.Int64
module I32 = FStar.Int32
module HS = FStar.HyperStack
module B = LowStar.Buffer

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

let is_elem_int (e:int) : GTot bool =
  let q = elem_v params_q in
  -q < e && e < q

let is_elem (e:elem_base) : GTot bool = let x = elem_v e in is_elem_int x
let is_elem_i32 (e:I32.t) : GTot bool = let x = I32.v e in is_elem_int x
let is_elem_i64 (e:I64.t) : GTot bool = let x = I64.v e in is_elem_int x

type elem = elem_base
let is_uelem e = let x = uelem_v e in let q = elem_v params_q in 0 <= x /\ x < q
type uelem = uelem_base
type poly = lbuffer elem params_n
type poly_k = lbuffer elem (params_k *! params_n)

let is_montgomery (e:elem) = 0 <= elem_v e /\ elem_v e < 2 * elem_v params_q
let is_corrected (e:elem) = -(elem_v params_q / 2) < elem_v e /\ elem_v e <= elem_v params_q / 2
let is_sampler_output (e:elem) = let b = pow2 (v params_s_bits-1) in -b <= elem_v e /\ elem_v e < b
let is_y_sampler_output (e:elem) = let b = elem_v params_B in -b <= elem_v e /\ elem_v e <= b
let is_pk (e:elem) = 0 <= elem_v e /\ elem_v e < elem_v params_q
//let is_sk (e:elem) = -(pow2 (v params_s_bits)) <= elem_v e /\ elem_v e < pow2 (v params_s_bits)
unfold let is_sk = is_sampler_output
let is_pmq (e:elem) = let q = elem_v params_q in -q < elem_v e /\ elem_v e < q
let is_z_accepted (e:elem) = let b = elem_v params_B in let s = elem_v params_U in -(b-s) <= elem_v e /\ elem_v e <= (b-s)
let is_sparse_mul_output (e:elem) = (-65536) <= elem_v e /\ elem_v e <= 65536 // [-2^16, 2^16]; see sparse_mul for comments
let is_sparse_mul32_output (e:elem) = let q = elem_v params_q in -q <= elem_v e /\ elem_v e < 2 * q

let is_poly_montgomery_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_montgomery (bget h p i)} is_montgomery (bget h p i)
let is_poly_corrected_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_corrected (bget h p i)}  is_corrected (bget h p i)
let is_poly_sampler_output_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_sampler_output (bget h p i)} is_sampler_output (bget h p i)
let is_poly_y_sampler_output_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_y_sampler_output (bget h p i)} is_y_sampler_output (bget h p i)
let is_poly_pk_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_pk (bget h p i)} is_pk (bget h p i)
//let is_poly_sk_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_sk (bget h p i)} is_sk (bget h p i)
unfold let is_poly_sk_i = is_poly_sampler_output_i
let is_poly_pmq_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_pmq (bget h p i)} is_pmq (bget h p i)
let is_poly_z_accepted_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_z_accepted (bget h p i)} is_z_accepted (bget h p i)
let is_poly_sparse_mul_output_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_sparse_mul_output (bget h p i)} is_sparse_mul_output (bget h p i)
let is_poly_sparse_mul32_output_i (h:HS.mem) (p:poly) (j:nat{j <= v params_n}) = forall (i:nat{i < j}). {:pattern is_sparse_mul32_output (bget h p i)} is_sparse_mul32_output (bget h p i)

let is_poly_k_montgomery_i (h:HS.mem) (p:poly_k) (j:nat{j <= v params_k * v params_n}) = forall (i:nat{i < j}). {:pattern is_montgomery (bget h p i)} is_montgomery (bget h p i)
let is_poly_k_corrected_i (h:HS.mem) (p:poly_k) (j:nat{j <= v params_k * v params_n}) = forall (i:nat{i < j}). {:pattern is_corrected (bget h p i)} is_corrected (bget h p i)
let is_poly_k_sampler_output_i (h:HS.mem) (p:poly_k) (j:nat{j <= v params_k * v params_n}) = forall (i:nat{i < j}). {:pattern is_sampler_output (bget h p i)} is_sampler_output (bget h p i)
let is_poly_k_pk_i (h:HS.mem) (p:poly_k) (j:nat{j <= v params_k * v params_n}) = forall (i:nat{i < j}). {:pattern is_pk (bget h p i)} is_pk (bget h p i)
//let is_poly_k_sk_i (h:HS.mem) (p:poly_k) (j:nat{j <= v params_k * v params_n}) = forall (i:nat{i < j}). {:pattern is_sk (bget h p i)} is_sk (bget h p i)
unfold let is_poly_k_sk_i = is_poly_sampler_output_i

let is_poly_montgomery (h:HS.mem) (p:poly) = is_poly_montgomery_i h p (v params_n)
let is_poly_corrected (h:HS.mem) (p:poly) = is_poly_corrected_i h p (v params_n)
let is_poly_sampler_output (h:HS.mem) (p:poly) = is_poly_sampler_output_i h p (v params_n)
let is_poly_y_sampler_output (h:HS.mem) (p:poly) = is_poly_y_sampler_output_i h p (v params_n)
let is_poly_pk (h:HS.mem) (p:poly) = is_poly_pk_i h p (v params_n)
//let is_poly_sk (h:HS.mem) (p:poly) = is_poly_sk_i h p (v params_n)
unfold let is_poly_sk = is_poly_sampler_output
let is_poly_pmq (h:HS.mem) (p:poly) = is_poly_pmq_i h p (v params_n)
let is_poly_z_accepted (h:HS.mem) (p:poly) = is_poly_z_accepted_i h p (v params_n)
let is_poly_sparse_mul_output (h:HS.mem) (p:poly) = is_poly_sparse_mul_output_i h p (v params_n)
let is_poly_sparse_mul32_output (h:HS.mem) (p:poly) = is_poly_sparse_mul32_output_i h p (v params_n)

let is_poly_k_montgomery (h:HS.mem) (p:poly_k) = is_poly_k_montgomery_i h p (v params_k * v params_n)
let is_poly_k_corrected (h:HS.mem) (p:poly_k) = is_poly_k_corrected_i h p (v params_k * v params_n)
let is_poly_k_sampler_output (h:HS.mem) (p:poly_k) = is_poly_k_sampler_output_i h p (v params_k * v params_n)
let is_poly_k_pk (h:HS.mem) (p:poly_k) = is_poly_k_pk_i h p (v params_k * v params_n)
//let is_poly_k_sk (h:HS.mem) (p:poly_k) = is_poly_k_sk_i h p (v params_k * v params_n)
unfold let is_poly_k_sk = is_poly_k_sampler_output

let is_poly_equal (h0 h1:HS.mem) (p:poly) = 
    forall (i:nat{i < v params_n}) . {:pattern bget h1 p i} bget h0 p i == bget h1 p i
let is_poly_equal_except (h0 h1:HS.mem) (p:poly) (k:nat{k < v params_n}) = 
    forall (i:nat{i < v params_n /\ i <> k}) . {:pattern bget h1 p i} bget h0 p i == bget h1 p i
let is_poly_k_equal (h0 h1:HS.mem) (p:poly_k) = 
    forall (i:nat{i < v params_n * v params_k}) . {:pattern bget h1 p i} bget h0 p i == bget h1 p i

let is_sparse_elem_sk (e:sparse_elem) = -(pow2 (v params_s_bits)) <= sparse_v e /\ sparse_v e < pow2 (v params_s_bits)
let is_s_sk (h:HS.mem) (s:lbuffer sparse_elem params_n) =
    forall (i:nat{i < v params_n}) . {:pattern is_sparse_elem_sk (bget h s i)} is_sparse_elem_sk (bget h s i)
let is_s_equal (h0 h1:HS.mem) (s:lbuffer sparse_elem params_n) =
    forall (i:nat{i < v params_n}) . {:pattern bget h1 s i} bget h0 s i == bget h1 s i
let is_e_sk (h:HS.mem) (e:lbuffer sparse_elem (params_n *! params_k)) =
    forall (i:nat{i < v params_n * v params_k}) . {:pattern is_sparse_elem_sk (bget h e i)} is_sparse_elem_sk (bget h e i)
let is_e_equal (h0 h1:HS.mem) (e:lbuffer sparse_elem (params_n *! params_k)) =
    forall (i:nat{i < v params_n}) . {:pattern bget h1 e i} bget h0 e i == bget h1 e i

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p: poly) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ modifies l h0 h1 /\ disjoint l (gsub p (size 0) (size i)))
    (ensures is_poly_sampler_output_i h1 p i)
    [SMTPat (is_poly_sampler_output_i h1 p i); SMTPat (modifies l h0 h1)] =
    assert(is_poly_equal h0 h1 p)*)

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p: B.lbuffer elem (v params_n)) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ B.modifies l h0 h1 /\ B.loc_disjoint l (B.loc_buffer p)) //(B.loc_buffer (B.gsub p 0ul (UI32.uint_to_t i))))
    (ensures is_poly_sampler_output_i h1 p i)
    [SMTPat (is_poly_sampler_output_i h1 p i); SMTPat (B.modifies l h0 h1)] = 
    assert(forall (j:nat{j < i}) . {:pattern B.get h1 p j} B.get h0 p j == B.get h1 p j)*)

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p: poly) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ B.modifies l h0 h1 /\ B.loc_disjoint l (loc ((gsub p (size 0) (size i)))))
    (ensures is_poly_sampler_output_i h1 p i)
    [SMTPat (is_poly_sampler_output_i h1 p i); SMTPat (modifies l h0 h1)] = admit()
    //assert(forall (j:nat{j < i}) . {:pattern bget h1 p j} bget h0 p j == bget h1 p j)
    //assert(is_poly_equal h0 h1 p)*)
    
val poly_create:
    unit
  -> StackInline poly
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> live h1 r /\ stack_allocated r h0 h1 (Seq.create (v params_n) (to_elem 0)))

let poly_create _ = create params_n (to_elem 0)

val poly_k_create:
    unit
  -> StackInline poly_k
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> live h1 r /\ stack_allocated r h0 h1 (Seq.create (v params_n * v params_k) (to_elem 0)))

let poly_k_create _ = create (params_n *! params_k) (to_elem 0)

val get_poly: p: poly_k -> k: size_t{k <. params_k} -> GTot poly
let get_poly p k = gsub p (k *! params_n) params_n

inline_for_extraction noextract
val index_poly: p: poly_k -> k: size_t{k <. params_k} -> Stack poly
    (requires fun h -> live h p)
    (ensures  fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == gsub p (k *! params_n) params_n /\
                          loc_includes (loc p) (loc r))
let index_poly p k = sub p (k *! params_n) params_n

val reduce:
    a: I64.t{let q = elem_v params_q in let va = I64.v a in va <= (q-1)*(q-1)}
  -> Tot (r:elem{is_montgomery r})

let reduce a =
    // Patrick says even if this multiplication overflows, the bottom 32 bits, which we then mask off, are still
    // correct -- as in, if the multiplication were contained in a larger machine integer that could not overflow from
    // the multiplication of two Int64s, the bottom 32 bits are the same.

    // According to Jonathan, overflow on signed integer types is undefined behavior, even if we know the contents are
    // nonnegative. But since we know the contents are nonnegative, we instead cast to unsigned types and do the
    // multiplication which, if it overflows, has a well-defined behavior.
    [@inline_let] let aUnsigned = FStar.Int.Cast.int64_to_uint64 a in
    [@inline_let] let params_qinv_unsigned = FStar.Int.Cast.int64_to_uint64 params_qinv in
    let u:I64.t = FStar.Int.Cast.uint64_to_int64 UI64.((aUnsigned *%^ params_qinv_unsigned) &^ 0xFFFFFFFFuL) in
    lemma_logand32_value_max UI64.(aUnsigned *%^ params_qinv_unsigned);
    lemma_logand32_value_min UI64.(aUnsigned *%^ params_qinv_unsigned);
    assert(I64.v u <= pow2 32 - 1);
    let u:I64.t = I64.(u *^ (elem_to_int64 params_q)) in
    assert(I64.v u <= (pow2 32 - 1) * elem_v params_q);
    let a:I64.t = I64.(a +^ u) in
    //assume(I64.v I64.(a >>^ 32ul) == I64.v a / pow2 32); 
    //assume(let result = I64.v I64.(a >>^ 32ul) in let q = elem_v params_q in -q < result /\ result < q);
    //assume(let result = I64.(a >>^ 32ul) in is_montgomery (int64_to_elem result));
    assume(0 <= I64.v a);
    shift_right_value_lemma_int64 a 32ul;
    assert(is_montgomery (int64_to_elem (I64.(a >>^ 32ul))));
    int64_to_elem I64.(a >>^ 32ul)


val barr_reduce:
    a: elem_base
  -> Tot elem

// Output range of barr_reduce is [-q, 2q] per Patrick
let barr_reduce a =
    let a64:I64.t = elem_to_int64 a in
    let u:elem_base = (int64_to_elem I64.((a64 *^ params_barr_mult) >>>^ params_barr_div)) in
    assume(FStar.Int.fits (elem_v u * elem_v params_q) elem_n);
    assume(is_elem_int (elem_v a - elem_v u * elem_v params_q));
    a -^ u *^ params_q

(** Modification four buffers -- taken from Lib.Buffer.fsti *)
let modifies4 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3) (h1 h2: HyperStack.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3) h1 h2

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

inline_for_extraction noextract
val unsafe_declassify:
    #t:inttype
  -> us: uint_t t SEC
  -> Tot (up:uint_t t PUB{uint_v us == uint_v up})

let unsafe_declassify #t us =
    match t with
    | U1   -> Lib.RawIntTypes.u8_to_UInt8 (cast U8 SEC us)
    | U8   -> Lib.RawIntTypes.u8_to_UInt8 us
    | U16  -> Lib.RawIntTypes.u16_to_UInt16 us
    | U32  -> Lib.RawIntTypes.u32_to_UInt32 us
    | U64  -> Lib.RawIntTypes.u64_to_UInt64 us
    | U128 -> Lib.RawIntTypes.u128_to_UInt128 us

let buf = t:buftype & a:Type0 & buffer_t t a 
[@BigOps.__reduce__] unfold
noextract let bb (#t:buftype) (#a:Type0) (b:buffer_t t a) : GTot buf = (| t, a, b |)
[@BigOps.__reduce__] unfold
let disjoint_buf (b0 b1: buf) =
  let (| _, _, b0 |) = b0 in
  let (| _, _, b1 |) = b1 in
  disjoint b0 b1
[@BigOps.__reduce__] unfold
let live_buf (h:HS.mem) (b: buf) =
  let (| _, _, b |) = b in
  live h b

private let shift_arithmetic_left_value_check (x:elem) (s:UI32.t{UI32.v s < elem_n}) =
    elem_v x * pow2 (UI32.v s) >= Int.min_int elem_n /\
    elem_v x * pow2 (UI32.v s) <= Int.max_int elem_n

inline_for_extraction noextract
val shift_arithmetic_left:
    x : elem
  -> s : UI32.t{v s < elem_n}// /\ shift_arithmetic_left_value_check x s}
  -> Tot I32.t // (r:I32.t{I32.v r == I32.v x * pow2 (UI32.v s)})

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2"

let shift_arithmetic_left x s =
    uelem_to_elem ((elem_to_uelem x) `uelem_sl` s)
    //let r = FStar.Int.Cast.uint32_to_int32 UI32.((FStar.Int.Cast.int32_to_uint32 x) <<^ s) in
    //Int.shift_left_value_lemma (I32.v x) (UI32.v s);
    //assert(I32.v r == I32.v x * pow2 (UI32.v s));
    //r

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p: poly) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ modifies l h0 h1 /\ disjoint l (gsub p (size 0) (size i)))
    (ensures is_poly_sampler_output_i h1 p i)
    [SMTPat (is_poly_sampler_output_i h1 p i); SMTPat (modifies l h0 h1)] =
    assert(is_poly_equal h0 h1 p)*)

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p: B.lbuffer elem (v params_n)) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ B.modifies l h0 h1 /\ B.loc_disjoint l (B.loc_buffer p)) //(B.loc_buffer (B.gsub p 0ul (UI32.uint_to_t i))))
    (ensures is_poly_sampler_output_i h1 p i)
    [SMTPat (is_poly_sampler_output_i h1 p i); SMTPat (B.modifies l h0 h1)] = 
    assert(forall (j:nat{j < i}) . {:pattern B.get h1 p j} B.get h0 p j == B.get h1 p j)*)

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p: poly) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ B.modifies l h0 h1 /\ B.loc_disjoint l (loc ((gsub p (size 0) (size i)))))
    (ensures is_poly_sampler_output_i h1 p i)
    [SMTPat (is_poly_sampler_output_i h1 p i); SMTPat (modifies l h0 h1)] = admit()
    //assert(forall (j:nat{j < i}) . {:pattern bget h1 p j} bget h0 p j == bget h1 p j)
    //assert(is_poly_equal h0 h1 p)*)

(*let frame_is_poly_sampler_output_i (h0 h1: HS.mem) (p:poly) (i:nat{i <= v params_n}) (l:B.loc) : Lemma
    (requires is_poly_sampler_output_i h0 p i /\ B.modifies l h0 h1 /\ B.loc_disjoint l (loc p))
    (ensures is_poly_sampler_output_i h1 p i) = 
    assert(forall (j:nat{j < i}) . {:pattern bget h1 p j} bget h0 p j == bget h1 p j)*)
