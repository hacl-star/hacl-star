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
open Hacl.Impl.QTesla.Lemmas

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

inline_for_extraction noextract
let ntt = Hacl.Impl.QTesla.Heuristic.Poly.ntt

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
           assume(is_elem (temp +^ ajNumo));
           a.(j) <- temp +^ ajNumo; // TODO (kkane): This line is where I differs from III-size and III-speed.
           assume(FStar.Int.fits (elem_v temp - elem_v ajNumo) elem_n);
           [@inline_let] let difference = temp -^ ajNumo in
           assume(Int.fits (elem_v wj * elem_v difference) I64.n);
           [@inline_let] let product = I64.((elem_to_int64 wj) *^ (elem_to_int64 difference)) in
           assume(let q = elem_v params_q in I64.v product >= 0 /\ I64.v product <= (q-1)*(q-1));
           a.(jNumo) <- reduce product;
           jBuf.(size 0) <- j +. size 1
       );
    let res = jBuf.(size 0) in
    pop_frame();
    res

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
        assume(let q = elem_v params_q in let r = I64.v params_r in let result = r * elem_v ai in
               result >= 0 /\ result <= (q-1)*(q-1));
	a.(i) <- reduce I64.(params_r *^ (elem_to_int64 ai))
    );

    pop_frame()

private val move_refinement: #a:Type -> #p:(a -> Type)
  -> l:list a{forall z. FStar.List.Tot.Base.memP z l ==> p z} -> list (x:a{p x})
let rec move_refinement #a #p = function
  | [] -> []
  | hd :: tl -> hd :: move_refinement #a #p tl

private let rec list_of_elem l : GTot bool =
    match l with
    | [] -> true
    | hd :: tl -> is_elem hd && list_of_elem tl

private val list_of_elem_memP: l:list elem_base -> Lemma 
  (requires list_of_elem l)
  (ensures (forall x. FStar.List.Tot.Base.memP x l ==> is_elem x))
let rec list_of_elem_memP = function
  | [] -> ()
  | x :: tl -> list_of_elem_memP tl

private unfold val coerce: l:list elem_base{list_of_elem l} -> list elem
let coerce l =
  list_of_elem_memP l;
  normalize_term (move_refinement l)

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 0"

//let test _ = assert_norm(list_of_elem zeta_list); coerce zeta_list

val poly_ntt:
    x_ntt: poly
  -> x: poly
  -> Stack unit
    (requires fun h -> live h x_ntt /\ live h x /\ disjoint x_ntt x /\ is_poly_pmq h x)
    (ensures fun h0 _ h1 -> modifies1 x_ntt h0 h1 /\ is_poly_montgomery h1 x_ntt)

let poly_ntt x_ntt x =
    let hInit = ST.get () in
    push_frame();
    (* 
    When the Frodo code creates arrays of constants like this, it uses createL_global, which creates an
    immutable buffer. But this screws up subtyping with poly, which is sometimes mutable. Nik tells us
    there's no good way to do this because, unlike const parameters in C, guarantees like this go both ways
    and we'd essentially be asking the world never to mutate a poly, which is obviously not going to work. So
    we use createL, which makes it mutable, but we just never change it.
    *)
    assert_norm(list_of_elem zeta_list);
    [@inline_let] let (zeta_list_elem:list elem) = coerce zeta_list in 
    let zeta : poly = createL zeta_list_elem in 
    let h0 = ST.get() in
    assert(is_poly_equal hInit h0 x);
    for 0ul params_n
    (fun h i -> live h x_ntt /\ live h x /\ modifies1 x_ntt h0 h /\ is_poly_pmq h x /\ i <= v params_n /\ is_poly_pmq_i h x_ntt i)
    (fun i ->
        let h1 = ST.get () in
        assert(is_pmq (bget h1 x (v i)));
        x_ntt.(i) <- x.(i);
        let h2 = ST.get () in 
        assert(bget h2 x_ntt (v i) = bget h2 x (v i));
        assert(is_poly_equal h1 h2 x);
        assert(is_poly_equal_except h1 h2 x_ntt (v i));
        assert(is_pmq (bget h2 x_ntt (v i)));
        assert(is_poly_pmq_i h2 x_ntt (v i + 1))
    );

    ntt x_ntt zeta;
    let hNtt = ST.get () in
    pop_frame();
    let hReturn = ST.get () in
    assert(is_poly_equal hNtt hReturn x_ntt)

inline_for_extraction noextract
let poly_pointwise = Hacl.Impl.QTesla.Heuristic.Poly.poly_pointwise

// Unlike the reference code, this version of poly_mul assumes both arguments are in NTT form.
val poly_mul:
    result: poly
  -> x: poly
  -> y: poly
  -> Stack unit
    (requires fun h -> live h result /\ live h x /\ live h y /\ disjoint result x /\ disjoint result y /\ disjoint x y /\
                    is_poly_montgomery h x /\ is_poly_montgomery h y)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ is_poly_montgomery h1 result)

let poly_mul result x y =
    let hInit = ST.get () in
    push_frame(); 
    assert_norm(list_of_elem zetainv_list);
    [@inline_let] let (zetainv_list_elem:list elem) = coerce zetainv_list in
    let zetainv : poly = createL zetainv_list_elem in
    let hPointwise = ST.get () in
    assert(is_poly_equal hInit hPointwise x);
    assert(is_poly_equal hInit hPointwise y);
    poly_pointwise result x y;
    nttinv result zetainv;
    pop_frame();
    let h1 = ST.get () in
    assume(is_poly_montgomery h1 result)

inline_for_extraction noextract
let poly_add = Hacl.Impl.QTesla.Heuristic.Poly.poly_add

inline_for_extraction noextract
let poly_add_correct = Hacl.Impl.QTesla.Heuristic.Poly.poly_add_correct

inline_for_extraction noextract
let poly_sub_correct = Hacl.Impl.QTesla.Heuristic.Poly.poly_sub_correct

inline_for_extraction noextract
let poly_sub_reduce = Hacl.Impl.QTesla.Heuristic.Poly.poly_sub_reduce
