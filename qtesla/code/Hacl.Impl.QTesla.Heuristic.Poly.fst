module Hacl.Impl.QTesla.Heuristic.Poly

open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
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
module LL = Lib.Loops

open C.Loops
module CL = C.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Platform
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals
open Hacl.Impl.QTesla.Lemmas

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract private
val ntt_innerfor:
    numoProblems: size_t{v numoProblems > 0 /\ v numoProblems <= v params_n / 2}
  -> jFirst: size_t{v jFirst + 2 * v numoProblems <= v params_n}
  -> a: poly
  -> wj: elem
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures fun h0 r h1 -> modifies1 a h0 h1 /\ v r = v jFirst + v numoProblems)

let ntt_innerfor numoProblems jFirst a wj =
    push_frame();
    let jBuf = create (size 1) jFirst in
    let liveness h = live h jBuf /\ live h a in
    let h0 = ST.get() in
    LL.while
        (fun h -> liveness h /\ modifies2 a jBuf h0 h /\ v (bget h jBuf 0) <= v jFirst + v numoProblems)
        (fun h -> v (bget h jBuf 0) < v jFirst + v numoProblems)
        (fun _ -> jBuf.(size 0) <. jFirst +. numoProblems)
        (fun _ ->
            let j = jBuf.(size 0) in
            let jNumo = j +. numoProblems in
            let ajNumo:elem = a.(jNumo) in // a[j + NumoProblems]
            let h1 = ST.get() in
            assume(elem_product_fits_int64 wj (bget h1 a (v jNumo)));
            //lemma_elem_product_fits_int64 wj (bget h1 a (v jNumo));
            let product = I64.((elem_to_int64 wj) *^ (elem_to_int64 ajNumo)) in
            assume(FStar.Int.fits (I64.v product * I64.v params_qinv) I64.n);
            assume(let q = elem_v params_q in I64.v product <= (q-1)*(q-1) /\ I64.v product >= 0);
            let temp:elem = reduce product in
            let aj:elem = a.(j) in
            assume(is_elem_int (elem_v aj - elem_v temp));
            a.(jNumo) <- aj -^ temp;
            assume(is_elem_int (elem_v temp + elem_v aj));
            a.(j) <- temp +^ aj;
	    jBuf.(size 0) <- j +. size 1;
            let h2 = ST.get() in
            let newjVal = v (bget h2 jBuf 0) in
            assert(newjVal <= v jFirst + v numoProblems)
        );
    let h2 = ST.get() in
    assert(v (bget h2 jBuf 0) = v jFirst + v numoProblems);
    let res = jBuf.(size 0) in
    pop_frame();
    assert(v res = v jFirst + v numoProblems);
    res

inline_for_extraction noextract private
val ntt_middlefor:
    numoProblems: size_t{v numoProblems > 0 /\ v numoProblems <= v params_n / 2}
  -> jTwiddle: lbuffer size_t (size 1)
  -> w: poly
  -> a: poly
  -> Stack unit
    (requires fun h -> live h jTwiddle /\ live h w /\ live h a /\
                    disjoint jTwiddle w /\ disjoint jTwiddle a /\ disjoint w a /\
                    v (bget h jTwiddle 0) < v params_n - (v params_n / (2 * v numoProblems)))
    (ensures fun h0 _ h1 -> modifies2 a jTwiddle h0 h1 /\
                         v (bget h1 jTwiddle 0) = v (bget h0 jTwiddle 0) + (v params_n / (2 * v numoProblems)))

let ntt_middlefor numoProblems jTwiddle w a =
    push_frame();
    let jFirst = create (size 1) (size 0) in
    let h0 = ST.get() in
    assert(v (bget h0 jTwiddle 0) < v params_n);
    LL.while
        (fun h -> live h jTwiddle /\ live h jFirst /\ live h a /\ live h w /\ modifies3 a jTwiddle jFirst h0 h)// /\
               //(v (bget h jFirst 0) < v params_n ==> v (bget h jTwiddle 0) < v params_n))
        (fun h -> v (bget h jFirst 0) < v params_n)
        (fun _ -> jFirst.(size 0) <. params_n)
        (fun _ ->
            let h0 = ST.get() in
            (* Proof note: This loop runs (params_n/(2*numoProblems)) times. Both are always powers of 2 and numoProblems
             * is always smaller by at least one factor of 2, going all the way down to 1. jTwiddle has been incremented
             * by (params_n/2*numoProblems) by the time the loop ends.
             *)
            let jTwiddleVal = jTwiddle.(size 0) in
            assume(v jTwiddleVal < v params_n);
            let wj:elem = w.(jTwiddleVal) in
            jTwiddle.(size 0) <- jTwiddleVal +. size 1;
            let h1 = ST.get() in
            assume(v (bget h1 jFirst 0) + 2 * v numoProblems <= v params_n);
            // The reference code uses the value for j to increment jFirst, so we follow suit, but j is always
            // equal to the previous value of jFirst + numoProblems.
            let j = ntt_innerfor numoProblems jFirst.(size 0) a wj in
            let h2 = ST.get() in
            assert(v j = v (bget h2 jFirst 0) + v numoProblems);
            jFirst.(size 0) <- j +. numoProblems;
            let h3 = ST.get() in
            assert(v (bget h3 jFirst 0) = v (bget h2 jFirst 0) + 2 * v numoProblems)
        );
    let h3 = ST.get() in
    assume(v (bget h3 jTwiddle 0) = v (bget h0 jTwiddle 0) + (v params_n / (2 * v numoProblems)));
    pop_frame()
        
val ntt:
    a: poly
  -> w: poly
  -> Stack unit
    (requires fun h -> live h a /\ live h w /\ disjoint a w)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1 /\ is_poly_montgomery h1 a)

let ntt a w =
    push_frame();
    let numoProblems = create (size 1) (params_n >>. (size 1)) in
    let jTwiddle = create (size 1) (size 0) in
    let h0 = ST.get() in
    LL.while
        (fun h -> live h numoProblems /\ live h jTwiddle /\ live h a /\ live h w /\ modifies3 numoProblems jTwiddle a h0 h /\
               v (bget h numoProblems 0) <= (v params_n / 2))
        (fun h -> v (bget h numoProblems 0) > 0)
        (fun _ -> numoProblems.(size 0) >. (size 0))
        (fun _ ->
        (* Proof note: We need to track the value of jTwiddle. This loop will always run for log2(params_n) + 1 iterations.
         * Each call to ntt_middlefor increments jTwiddle by (params_n/(2*numoProblems)). Need to prove this is always < params_n.
         *)
            let h1 = ST.get() in
            assume(v (bget h1 jTwiddle 0) < v params_n - (v params_n / (2 * v (bget h1 numoProblems 0))));
            ntt_middlefor numoProblems.(size 0) jTwiddle w a;
            let h2 = ST.get() in
            assert(v (bget h2 jTwiddle 0) = v (bget h1 jTwiddle 0) + (v params_n / (2 * v (bget h1 numoProblems 0))));
            assert(v (bget h2 jTwiddle 0) < v params_n);
            numoProblems.(size 0) <- numoProblems.(size 0) >>. size 1
        );
    pop_frame();
    let hReturn = ST.get () in
    assume(is_poly_montgomery hReturn a)

/// Inverse NTT implementation only for III-speed and III-size; I has its own which is slightly different.

inline_for_extraction noextract private
val nttinv_innerfor:
    numoProblems: size_t{v numoProblems > 0 /\ v numoProblems <= v params_n / 2}
  -> jFirst: size_t{v jFirst + 2 * v numoProblems < v params_n}
  -> a: poly
  -> wj: elem
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)

let nttinv_innerfor numoProblems jFirst a wj = 
    push_frame();
    assert(v numoProblems > 0);
    assert(v jFirst + v numoProblems > v jFirst);
    assert(v jFirst + v numoProblems = v (jFirst +. numoProblems));
    let jBuf = create (size 1) jFirst in
    let liveness h = live h jBuf /\ live h a in
    let h0 = ST.get() in
    assert(bget h0 jBuf 0 <. params_n);
    LL.while
       (fun h -> liveness h /\ v (bget h jBuf 0) < v params_n /\ modifies2 jBuf a h0 h /\
              v jFirst + 2 * v numoProblems < v params_n)
       (fun h -> v (bget h jBuf 0) < v jFirst + v numoProblems)
       (fun _ -> jBuf.(size 0) <. jFirst +. numoProblems)
       (fun _ -> 
           let j:size_t = jBuf.(size 0) in
           let jNumo = j +. numoProblems in
           let temp:elem = a.(j) in
           let ajNumo:elem = a.(jNumo) in
           assume(FStar.Int.fits (elem_v temp + elem_v ajNumo) elem_n);
	   if numoProblems = size 16
	   then ( a.(j) <- barr_reduce ( temp +^ ajNumo ) )
	   else ( a.(j) <- temp +^ ajNumo );
           assume(FStar.Int.fits (elem_v temp - elem_v ajNumo) elem_n);
           [@inline_let] let difference = temp -^ ajNumo in
           assume(elem_product_fits_int64 wj difference);
           //lemma_elem_product_fits_int64 wj difference;
           [@inline_let] let product = I64.((elem_to_int64 wj) *^ (elem_to_int64 difference)) in
           assume(FStar.Int.fits (I64.v product * I64.v params_qinv) I64.n);
           assume(let q = elem_v params_q in let p = I64.v product in p >= 0 /\ p <= (q-1)*(q-1));
           a.(jNumo) <- reduce product;
           jBuf.(size 0) <- j +. size 1
       );
    let res = jBuf.(size 0) in
    pop_frame();
    res

inline_for_extraction noextract private
val nttinv_middlefor:
    numoProblems: size_t{v numoProblems > 0 /\ v numoProblems <= v params_n / 2}
  -> jTwiddle: lbuffer size_t (size 1)
  -> w: poly
  -> a: poly
  -> Stack unit
    (requires fun h -> live h jTwiddle /\ live h w /\ live h a /\ v (bget h jTwiddle 0) < v params_n)
    (ensures fun h0 _ h1 -> modifies2 jTwiddle a h0 h1)

let nttinv_middlefor numoProblems jTwiddle w a =
    push_frame();
    let jFirst = create (size 1) (size 0) in
    let cond () : Stack bool
      (requires fun h -> live h jFirst)
      (ensures fun h0 _ h1 -> live h1 jFirst)
    = jFirst.(size 0) <. params_n in
    let liveness h = live h jTwiddle /\ live h jFirst /\ live h a /\ live h w in
    let h0 = ST.get() in
    LL.while // Middle for loop
        (fun h -> liveness h /\ modifies3 jFirst jTwiddle a h0 h)
        (fun h -> v (bget h jFirst 0) < v params_n)
        (fun _ -> jFirst.(size 0) <. params_n)
        (fun _ ->
            let jTwiddleVal = jTwiddle.(size 0) in
            assume(v jTwiddleVal < v params_n);
            let wj:elem = w.(jTwiddleVal) in
            jTwiddle.(size 0) <- jTwiddleVal +. (size 1);
            // TODO (kkane): I *think* j should always be equal to jFirst + numoProblems when it returns, but the
            // reference code uses j + numoProblems to increment jFirst, and I'm too afraid to deviate
            // at all from it right now. :)
            let h = ST.get() in
            assume(v (bget h jFirst 0) + 2 * v numoProblems < v params_n);
            let j = nttinv_innerfor numoProblems jFirst.(size 0) a wj in
            jFirst.(size 0) <- j +. numoProblems
        );
    pop_frame()
    
val nttinv:
    a: poly
  -> w: poly
  -> Stack unit
    (requires fun h -> live h a /\ live h w /\ disjoint a w)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)

let nttinv a w =
    push_frame();
    let numoProblems:lbuffer size_t (size 1) = create (size 1) (size 1) in
    let jTwiddle = create (size 1) (size 0) in

    let test_pre h = live h numoProblems /\ live h jTwiddle /\ live h a /\ live h w in
    (*let guard () : Stack bool
      (requires fun h -> live h numoProblems)
      (ensures fun h0 _ h1 -> h0 == h1)
      = numoProblems.(size 0) <. params_n in*)

    let h0 = ST.get() in
    LL.while // Outermost for loop
        (fun h -> test_pre h /\ modifies3 numoProblems jTwiddle a h0 h)
        (fun h -> v (bget h numoProblems 0) < v params_n)
        (fun _ -> numoProblems.(size 0) <. params_n)
        (fun _ ->
            let h1 = ST.get() in
            assume(v (bget h1 numoProblems 0) > 0);
            assume(v (bget h1 numoProblems 0) <= v params_n / 2);
            assume(v (bget h1 jTwiddle 0) < v params_n);
            nttinv_middlefor numoProblems.(size 0) jTwiddle w a;
            numoProblems.(size 0) <- numoProblems.(size 0) *. size 2
        );

    let h1 = ST.get() in
    for 0ul (params_n /. size 2)
    (fun h _ -> live h a /\ modifies1 a h1 h)
    (fun i ->
        assert_norm(v params_n / 2 < v params_n);
        assume(v i < v params_n);
        let ai = a.(i) in
        assume(let q = elem_v params_q in let r = I64.v params_r in let aiVal = elem_v ai in r * aiVal >= 0 /\ r * aiVal <= (q-1)*(q-1));
	a.(i) <- reduce I64.(params_r *^ (elem_to_int64 ai))
    );

    pop_frame()

val poly_pointwise:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1)

let poly_pointwise result x y =
    push_frame();
    let h0 = ST.get() in
    for (size 0) params_n
    (fun h _ -> live h result /\ live h x /\ live h y /\ modifies1 result h0 h)
    (fun i ->
        let xi:elem = x.(i) in
        let yi:elem = y.(i) in
        assume(FStar.Int.fits (elem_v xi * elem_v yi) I64.n);
        assume(let q = elem_v params_q in let r = elem_v xi * elem_v yi in r >= 0 /\ r <= (q-1)*(q-1));
        result.(i) <- reduce I64.( (elem_to_int64 xi) *^ (elem_to_int64 yi) )
    );
    pop_frame()

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

val poly_add:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result x /\ disjoint result y /\ disjoint x y /\
                    (forall (i:nat{i < v params_n}) . is_elem_int (elem_v (bget h x i) + elem_v (bget h y i))))
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ is_poly_pmq h1 result)

let poly_add result x y =
    push_frame();
    let h0 = ST.get() in
    for 0ul params_n
    (fun h i -> live h result /\ live h x /\ live h y /\ modifies1 result h0 h /\ i <= v params_n /\ is_poly_pmq_i h result i /\
             (forall (i:nat{i < v params_n}) . is_elem_int (elem_v (bget h x i) + elem_v (bget h y i))))
    (fun i -
        let h = ST.get () in assert(is_elem_int (elem_v (bget h x (v i)) + elem_v (bget h y (v i))));
        result.(i) <- x.(i) +^ y.(i);
        let hLoopEnd = ST.get () in
        assert(forall (j:nat{j < v params_n /\ j <> v i}) . bget h result j == bget hLoopEnd result j);
        assert(is_pmq (bget hLoopEnd result (v i)))
    );
    let hFinal = ST.get () in
    assert(is_poly_pmq hFinal result);
    pop_frame();
    let hReturn = ST.get () in
    assert(is_poly_equal hFinal hReturn result)
    
val poly_add_correct:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ is_poly_pk h1 result)

let poly_add_correct result x y =
    let h0 = ST.get() in
    for 0ul params_n
    (fun h _ -> live h result /\ live h x /\ live h y /\ modifies1 result h0 h)
    (fun i ->
        let h1 = ST.get () in 
        assume(FStar.Int.fits ((elem_v (bget h1 x (v i))) + (elem_v (bget h1 y (v i)))) elem_n);
        let temp:elem_base = x.(i) +^ y.(i) in
        assert_norm(size elem_n -. size 1 <. size I32.n);
        assume(elem_v temp >= 0);
        [@inline_let] let shiftresult = temp >>^ (size elem_n -. size 1) in
        //assert_norm(elem_v shiftresult == -1 \/ elem_v shiftresult == 0);
        //assert(elem_v temp < 0 <==> elem_v shiftresult == -1);
        //assert(elem_v temp >= 0 <==> elem_v shiftresult == 0);
        [@inline_let] let andresult = shiftresult &^ params_q in
        //assume(forall (x:elem) . (elem_v (to_elem (-1) &^ x)) == elem_v x);
        //assert(elem_v temp < 0 ==> elem_v shiftresult == (-1));
        //assert(elem_v temp < 0 ==> elem_v (shiftresult &^ params_q) == elem_v params_q);
        //assert(elem_v temp < 0 ==> elem_v andresult == elem_v params_q);
        //assert(elem_v andresult == elem_v params_q <==> elem_v temp < 0);
        //assume((elem_v ((to_elem (-1)) &^ params_q)) == elem_v params_q); 
        //assert(elem_v andresult == elem_v params_q \/ elem_v andresult == 0);
        assume(FStar.Int.fits (elem_v temp + elem_v andresult) I32.n);
	let temp:elem_base = temp +^ andresult in
        assume(FStar.Int.fits (elem_v temp - elem_v params_q) I32.n);
	let temp:elem_base = temp -^ params_q in
        assume(elem_v temp >= 0);
        [@inline_let] let addend = ((temp >>^ (size elem_n -. size 1)) &^ params_q) in
        assume(is_elem_int (elem_v temp + elem_v addend));
	let temp:elem = temp +^ ((temp >>^ (size elem_n -. size 1)) &^ params_q) in
        result.(i) <- temp
    );
    let hReturn = ST.get () in
    assume(is_poly_pk hReturn result)

val poly_sub_correct:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ is_poly_montgomery h1 result)

let poly_sub_correct result x y =
    push_frame();
    let h0 = ST.get() in
    for 0ul params_n
    (fun h _ -> live h result /\ live h x /\ live h y /\ modifies1 result h0 h)
    (fun i ->
        let h1 = ST.get () in 
        assume(FStar.Int.fits ((elem_v (bget h1 x (v i))) - (elem_v (bget h1 y (v i)))) elem_n);    
        let temp:elem_base = x.(i) -^ y.(i) in
        assert_norm(size elem_n -. size 1 <. size I32.n);
        assume(elem_v temp >= 0);
        assume(FStar.Int.fits (elem_v temp + elem_v ((temp >>^ (size elem_n -. size 1)) &^ params_q)) elem_n);
        let temp:elem_base = temp +^ ((temp >>^ (size elem_n -. size 1)) &^ params_q) in
        assume(is_elem temp);
        result.(i) <- temp
    );
    pop_frame();
    let hReturn = ST.get () in
    assume(is_poly_montgomery hReturn result)

// This function is sometimes used with result and x the same, so we can't assume they are disjoint.
val poly_sub_reduce:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result y /\ (disjoint x result \/ result == x) /\
                    is_poly_montgomery h x /\ is_poly_sparse_mul32_output h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ is_poly_montgomery h1 result)

let poly_sub_reduce result x y =
    let hInit = ST.get () in
    push_frame();
    let h0 = ST.get() in
    assert(is_poly_equal hInit h0 x);
    assert(is_poly_equal hInit h0 y);
    for 0ul params_n
    (fun h i -> live h result /\ live h x /\ live h y /\ i <= v params_n /\ modifies1 result h0 h /\ is_poly_montgomery_i h result i /\
             is_poly_sparse_mul32_output h y /\ is_poly_montgomery h x)
    (fun i ->
        let hBegin = ST.get () in
        assert(is_montgomery (bget hBegin x (v i)));
        assert(is_sparse_mul32_output (bget hBegin y (v i)));
        let xi = x.(i) in
        let yi = y.(i) in
        //assume(let q = elem_v params_q in let r = I64.v params_r in let result = r * (elem_v xi - elem_v yi) in
        //       result >= 0 /\ result <= (q-1)*(q-1));
        assert(elem_v xi >= 0 /\ elem_v xi < 2 * elem_v params_q);
        assert(let q = elem_v params_q in elem_v yi >= -q /\ elem_v yi < 2*q);
        assert(elem_v xi - elem_v yi <= 3 * elem_v params_q);
        result.(i) <- reduce I64.(params_r *^ ((elem_to_int64 xi) -^ (elem_to_int64 yi)));
        let hResult = ST.get () in
        assert(is_poly_equal_except hBegin hResult result (v i));
        assert(is_poly_montgomery_i hBegin result (v i));
        assert(is_montgomery (bget hResult result (v i)));
        assert(is_poly_equal hBegin hResult y);
        // TODO: This is tricky. Need to figure out how to prove:
        // if disjoint x result
        // 1. Trivial: x never changes, stays is_poly_montgomery the whole time
        // else x == result
        // 1. x started off is_poly_montgomery
        // 2. result therefore is is_poly_montgomery
        // 3. result.(i) we prove is_montgomery
        // 4. result therefore is still is_poly_montgomery
        assume(is_poly_montgomery hResult x)
    );
    let hFinal = ST.get () in
    pop_frame();
    let hReturn = ST.get () in
    assert(is_poly_equal hFinal hReturn result)
