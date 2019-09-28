module Hacl.Impl.QTesla.Provable.Poly

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

#reset-options "--z3rlimit_factor 4 --max_fuel 0 --max_ifuel 0"

unfold
let elem_op_ok (op: int -> int -> int) (x y:I32.t) = 
  FStar.Int.size (I32.v x `op` I32.v y) I32.n /\
  is_elem_int (I32.v x `op` I32.v y)
  
val poly_pointwise:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_pointwise result x y =
    let h0 = FStar.HyperStack.ST.get () in
    C.Loops.for (size 0) params_n
    (fun h _ -> modifies1 result h0 h)
    (fun i ->
        let xi:elem = x.(i) in
        let yi:elem = y.(i) in
        let _ = 
          let prod = (I64.v (elem_to_int64 xi) * I64.v (elem_to_int64 yi)) in
          assume (FStar.Int.size prod I64.n);
          assume (FStar.Int.fits (prod * I64.v params_qinv) I64.n)
        in
        result.(i) <- reduce I64.( (elem_to_int64 xi) *^ (elem_to_int64 yi) )
    )


val poly_add:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result x /\ disjoint result y /\ disjoint x y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_add result x y =
    let h0 = FStar.HyperStack.ST.get () in
    for 0ul params_n
    (fun h _ -> modifies1 result h0 h)
    (fun i ->
        let xi = x.(i) in
        let yi = y.(i) in
        assume (elem_op_ok (+) xi yi);
        result.(i) <- xi +^ yi
    )


// TODO: heuristic parameter sets have a poly_add_correct, poly_sub_correct, and poly_sub_reduce

val poly_sub:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_sub result x y =
    let h0 = FStar.HyperStack.ST.get () in
    for 0ul params_n
    (fun h _ -> modifies1 result h0 h)
    (fun i ->
        let xi:elem = x.(i) in
        let yi:elem = y.(i) in
        assume (elem_op_ok op_Subtraction xi yi);
        result.(i) <- barr_reduce (x.(i) -^ y.(i))
    )

val poly_add_correct:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result x /\ disjoint result y /\ disjoint x y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_add_correct result x y =
    let h0 = FStar.HyperStack.ST.get () in
    for 0ul params_n
        (fun h _ -> modifies1 result h0 h)
        (fun i ->
	    let xi = x.(i) in
	    let yi = y.(i) in
            assume (elem_op_ok (+) xi yi);
	    result.(i) <- xi +^ yi;
            let ri = result.(i) in
            assume (elem_op_ok op_Subtraction ri params_q);
	    result.(i) <- ri -^ params_q;
            let ri = result.(i) in
            assume (I32.v ri >= 0);
            let v  = ((ri >>^ (size elem_n) -. (size 1)) &^ params_q) in
            assume (elem_op_ok (+) ri v);
	    result.(i) <- ri +^ v
        )


// No correction in this parameter set for subtraction.
let poly_sub_correct result x y = poly_sub result x y

// No reduction in this parameter set for subtraction.
let poly_sub_reduce result x y = poly_sub result x y
