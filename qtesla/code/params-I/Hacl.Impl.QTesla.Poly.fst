module Hacl.Impl.QTesla.Poly

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

module B = LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open C.Loops
module LL = Lib.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals

inline_for_extraction noextract
let ntt = Hacl.Impl.QTesla.Heuristic.Poly.ntt

inline_for_extraction noextract private
val nttinv_innerfor:
    numoProblems: size_t{v numoProblems > 0 /\ v numoProblems < v params_n}
  -> jFirst: size_t{v jFirst + 2 * v numoProblems < v params_n}
  -> a: poly
  -> wj: elem
  -> Stack size_t
    (requires fun h -> live h a)
    (ensures fun h0 _ h1 -> True) //modifies1 a h0 h1)

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
       (fun h -> liveness h /\ v (bget h jBuf 0) < v params_n) //  /\ modifies1 a h0 h)
       (fun h -> v (bget h jBuf 0) < v jFirst + v numoProblems)
       (fun _ -> jBuf.(size 0) <. jFirst +. numoProblems)
       (fun _ -> 
           let j:size_t = jBuf.(size 0) in
           let jNumo = j +. numoProblems in
           let temp:elem = a.(j) in
           assume(v jNumo < v params_n);
           let ajNumo:elem = a.(jNumo) in
           assume(is_elem (temp +^ ajNumo));
           let h1 = ST.get() in
           a.(j) <- temp +^ ajNumo;
           [@inline_let] let difference = temp -^ ajNumo in
           assume(FStar.Int.fits (elem_v wj * elem_v difference) 64);
           [@inline_let] let product = I64.((elem_to_int64 wj) *^ (elem_to_int64 difference)) in
           assume(FStar.Int.fits (I64.v product * I64.v params_qinv) 64);
           a.(jNumo) <- reduce product;
           let h2 = ST.get() in
           assert(modifies1 a h1 h2);
           jBuf.(size 0) <- j +. size 1
       );
    let res = jBuf.(size 0) in
    pop_frame();
    res

inline_for_extraction noextract private
val nttinv_middlefor:
    numoProblems: size_t{v numoProblems > 0 /\ v numoProblems < v params_n}
  -> jTwiddle: lbuffer size_t (size 1)
  -> w: poly
  -> a: poly
  -> Stack unit
    (requires fun h -> live h jTwiddle /\ live h w /\ live h a /\ v (bget h jTwiddle 0) < v params_n)
    (ensures fun h0 _ h1 -> True) // modifies2 w a h0 h1)

let nttinv_middlefor numoProblems jTwiddle w a =
    push_frame();
    let jFirst = create (size 1) (size 0) in
    let cond () : Stack bool
      (requires fun h -> live h jFirst)
      (ensures fun h0 _ h1 -> live h1 jFirst)
    = jFirst.(size 0) <. params_n in
    let liveness h = live h jTwiddle /\ live h jFirst /\ live h a /\ live h w in
    LL.while // Middle for loop
        liveness
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
    (ensures fun h0 _ h1 -> True) // modifies1 a h0 h1)

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
    assert(v (bget h0 numoProblems 0) > 0);

    LL.while // Outermost for loop
        test_pre
        (fun h -> v (bget h numoProblems 0) < v params_n)
        (fun _ -> numoProblems.(size 0) <. params_n)
        (fun _ ->
            let h1 = ST.get() in
            assume(v (bget h1 numoProblems 0) > 0);
            assume(v (bget h1 numoProblems 0) < v params_n);
            assume(v (bget h1 jTwiddle 0) < v params_n);
            nttinv_middlefor numoProblems.(size 0) jTwiddle w a;
            numoProblems.(size 0) <- numoProblems.(size 0) *. size 2
        );

    for 0ul (params_n /. size 2)
    (fun h _ -> live h a)
    (fun i ->
        //assert(v i < v params_n / 2);
        assert_norm(v params_n / 2 < v params_n);
        assume(v i < v params_n);
        let ai = a.(i) in
        assume(FStar.Int.fits (I64.v params_r * elem_v ai * I64.v params_qinv) 64); 
	a.(i) <- reduce I64.(params_r *^ (elem_to_int64 ai))
    );

    pop_frame()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"


(*val nttinv:
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
    let guard () : Stack bool
      (requires fun h -> live h numoProblems)
      (ensures fun h0 _ h1 -> h0 == h1)
      = numoProblems.(size 0) <. params_n in

    while // Outermost for loop
        #test_pre
        #(fun _ h -> test_pre h)
        guard
        (fun _ ->
            push_frame();
            let jBuf = create (size 1) (size 0) in
            let jFirst = create (size 1) (size 0) in
            let cond () : Stack bool
              (requires fun h -> live h jFirst)
              (ensures fun h0 _ h1 -> live h1 jFirst)
            = jFirst.(size 0) <. params_n in
            let liveness h = live h numoProblems /\ live h jTwiddle /\ live h jBuf /\ live h jFirst /\ live h a /\ live h w in
            while // Middle for loop
                #(fun h -> liveness h /\ bget h jTwiddle 0 <. params_n)
                #(fun _ h -> liveness h /\ bget h jTwiddle 0 <. params_n)
                (fun _ -> jFirst.(size 0) <. params_n)
                (fun _ ->
                    let jTwiddleVal = jTwiddle.(size 0) in
                    let wj:elem = w.(jTwiddleVal) in
                    jTwiddle.(size 0) <- jTwiddleVal +. (size 1);
                    // Innermost for loop. Have to use a while because the middle for loop's increment depends on the
                    // final value of j from each inner for loop, so its scope can't be constrained to the for loop.
                    jBuf.(size 0) <- jFirst.(size 0);
                    let jFinish = jFirst.(size 0) +. numoProblems.(size 0) in
                    let liveness h = live h numoProblems /\ live h jTwiddle /\ live h jFirst /\ live h jBuf /\ live h a in
                    while
                        #(fun h -> liveness h /\ bget h jBuf 0 <. params_n)
                        #(fun _ h -> liveness h /\ bget h jBuf 0 <. params_n)
                        (fun _ -> jBuf.(size 0) <. jFinish)
                        (fun _ ->
                            let j:size_t = jBuf.(size 0) in
                            let jNumo = j +. numoProblems.(size 0) in
                            let temp:elem = a.(j) in
                            assume(jNumo <. params_n); // TODO
                            let ajNumo:elem = a.(jNumo) in
                            assume(elem_v temp + elem_v ajNumo < elem_v params_q);
                            assume(elem_v temp + elem_v ajNumo > -(elem_v params_q));
                            a.(j) <- temp +^ ajNumo;
                            a.(jNumo) <- reduce I64.((elem_to_int64 wj) *^ ((elem_to_int64 temp) -^ (elem_to_int64 ajNumo)));
                            jBuf.(size 0) <- j +. size 1
                        );
                    jFirst.(size 0) <- jBuf.(size 0) +. numoProblems.(size 0)
                );
            numoProblems.(size 0) <- numoProblems.(size 0) *. size 2;
            pop_frame()
        );

    for 0ul (params_n /. size 2)
    (fun h _ -> live h a)
    (fun i ->
        let ai = a.(i) in
        a.(i) <- reduce I64.(params_r *^ (elem_to_int64 ai))
    );

    pop_frame()
*)
val poly_ntt:
    x_ntt: poly
  -> x: poly
  -> Stack unit
    (requires fun h -> live h x_ntt /\ live h x /\ disjoint x_ntt x)
    (ensures fun h0 _ h1 -> modifies1 x h0 h1)

let poly_ntt x_ntt x =
    push_frame();
    (* 
    When the Frodo code creates arrays of constants like this, it uses createL_global, which creates an
    immutable buffer. But this screws up subtyping with poly, which is sometimes mutable. Nik tells us
    there's no good way to do this because, unlike const parameters in C, guarantees like this go both ways
    and we'd essentially be asking the world never to mutate a poly, which is obviously not going to work. So
    we use createL, which makes it mutable, but we just never change it.
    *)
    let zeta: poly = createL zeta_list in
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

let poly_mul result x y =
    push_frame();
    let zetainv : poly = createL zetainv_list in
    poly_pointwise result x y;
    nttinv result zetainv;
    pop_frame()

inline_for_extraction noextract
let poly_add = Hacl.Impl.QTesla.Heuristic.Poly.poly_add

inline_for_extraction noextract
let poly_add_correct = Hacl.Impl.QTesla.Heuristic.Poly.poly_add_correct

inline_for_extraction noextract
let poly_sub_correct = Hacl.Impl.QTesla.Heuristic.Poly.poly_sub_correct

inline_for_extraction noextract
let poly_sub_reduce = Hacl.Impl.QTesla.Heuristic.Poly.poly_sub_reduce
