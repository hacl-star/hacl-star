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
module I64 = FStar.Int64
module I32 = FStar.Int32

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

//let is_elem (e:elem_base) = let x = elem_v e in let q = elem_v params_q in -q < x /\ x < q

let is_elem_int (e:int) : GTot bool =
  let q = elem_v params_q in
  -q < e && e < q

(*assume IntTypeInequality : ~(I32.t == I64.t) /\ ~(I32.t == int) /\ ~(I64.t == int) 

let is_elem (#a:Type) (e:a) =
  let q = elem_v params_q in
  (a == I64.t \/ a == I32.t \/ a == int) /\
  ((a == I32.t) ==> (let x = I32.v e in is_elem_int x)) /\
  ((a == I64.t) ==> (let x = I64.v e in is_elem_int x)) /\
  ((a == int) ==> (is_elem_int e))*)

let is_elem (e:elem_base) : GTot bool = let x = elem_v e in is_elem_int x
let is_elem_i32 (e:I32.t) : GTot bool = let x = I32.v e in is_elem_int x
let is_elem_i64 (e:I64.t) : GTot bool = let x = I64.v e in is_elem_int x

//let test _ = let e:I32.t = 0l in assert(is_elem e)

//#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

type elem = e:elem_base{is_elem e}
let is_uelem e = let x = uelem_v e in let q = elem_v params_q in 0 <= x /\ x < q
type uelem = e:uelem_base{is_uelem e}
type poly = lbuffer elem params_n
type poly_k = lbuffer elem (params_k *. params_n)

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

let poly_k_create _ = create (params_n *. params_k) (to_elem 0)

unfold val get_poly: p: poly_k -> k: size_t{k <. params_k} -> GTot poly
let get_poly p k = gsub p (k *. params_n) params_n

unfold inline_for_extraction noextract
val index_poly: p: poly_k -> k: size_t{k <. params_k} -> Stack poly
    (requires fun h -> live h p)
    (ensures  fun h0 r h1 -> h0 == h1 /\ live h1 r /\ r == gsub p (size (v k * v params_n)) params_n /\
                          loc_includes (loc p) (loc r))
let index_poly p k = sub p (k *. params_n) params_n

val reduce:
    a: I64.t{FStar.Int.fits (I64.v a * I64.v params_qinv) I64.n}
  -> Tot elem

let reduce a =
    let u:I64.t = I64.((a *^ params_qinv) &^ 0xffffffffL) in
    lemma_logand32_value_max I64.(a *^ params_qinv);
    lemma_logand32_value_min I64.(a *^ params_qinv);
    let u:I64.t = I64.(u *^ (elem_to_int64 params_q)) in
    let a:I64.t = I64.(a +^ u) in
    assume(let result = I64.v I64.(a >>^ 32ul) in let q = elem_v params_q in -q < result /\ result < q);
    int64_to_elem I64.(a >>^ 32ul)

val barr_reduce:
    a: elem_base
  -> Tot elem

let barr_reduce a =
    let a64:I64.t = elem_to_int64 a in
    let u:elem_base = (int64_to_elem I64.((a64 *^ params_barr_mult) >>^ params_barr_div)) in
    assume(FStar.Int.fits (elem_v u * elem_v params_q) elem_n);
    assume(is_elem_int (elem_v a - elem_v u * elem_v params_q));
    a -^ u *^ params_q

(** Modification four buffers -- taken from Lib.Buffer.fsti *)
let modifies4 (#a0:Type0) (#a1:Type0) (#a2:Type0) (#a3:Type0)
  (b0:buffer_t MUT a0) (b1:buffer_t MUT a1) (b2:buffer_t MUT a2) (b3:buffer_t MUT a3) (h1 h2: HyperStack.mem) =
  modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3) h1 h2

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 1"

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
