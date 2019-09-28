module Hacl.Impl.QTesla.Poly

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

module I = FStar.Int
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module UI16 = FStar.UInt16
module UI32 = FStar.UInt32
module UI64 = FStar.UInt64
open FStar.Int.Cast

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open C.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

inline_for_extraction noextract
let ntt = Hacl.Impl.QTesla.Heuristic.Poly.ntt

inline_for_extraction noextract
let nttinv = Hacl.Impl.QTesla.Heuristic.Poly.nttinv

// When the Frodo code creates arrays of constants like this, it uses createL_global, which creates an
// immutable buffer. But this screws up subtyping with poly, which is sometimes mutable. Nik tells us
// there's no good way to do this because, unlike const parameters in C, guarantees like this go both ways
// and we'd essentially be asking the world never to mutate a poly, which is obviously not going to work. So
// we use createL, which makes it mutable, but we just never change it.
private let zeta: poly = createL zeta_list

val poly_ntt:
    x_ntt: poly
  -> x: poly
  -> Stack unit
    (requires fun h -> live h x_ntt /\ live h x /\ disjoint x_ntt x)
    (ensures fun h0 _ h1 -> modifies1 x h0 h1)

let poly_ntt x_ntt x =
    push_frame();
    for 0ul params_n
    (fun h _ -> live h x_ntt /\ live h x)
    (fun i ->
        x_ntt.(i) <- (x.(i))
    );

    ntt x_ntt zeta;
    pop_frame()

inline_for_extraction noextract
let poly_pointwise = Hacl.Impl.QTesla.Heuristic.Poly.poly_pointwise

// Unlike the reference code, this version of poly_mul assumes both arguments are in NTT form.
val poly_mul:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

private let zetainv: poly = createL zetainv_list

let poly_mul result x y =
    poly_pointwise result x y;
    nttinv result zetainv

inline_for_extraction noextract
let poly_add = Hacl.Impl.QTesla.Heuristic.Poly.poly_add

inline_for_extraction noextract
let poly_add_correct = Hacl.Impl.QTesla.Heuristic.Poly.poly_add_correct

inline_for_extraction noextract
let poly_sub_correct = Hacl.Impl.QTesla.Heuristic.Poly.poly_sub_correct

inline_for_extraction noextract
let poly_sub_reduce = Hacl.Impl.QTesla.Heuristic.Poly.poly_sub_reduce
