module Hacl.Impl.QTesla.Heuristic.Pack

open FStar.HyperStack
module HS = FStar.HyperStack
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
module B = LowStar.Buffer

open C.Loops
module LL = Lib.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals
module SP = QTesla.Params

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

// qTESLA-I and qTESLA-III-size share the implementation for: encode_pk decode_pk encode_sig decode_sig

[@"opaque_to_smt"]
private let valid_pk (pk: lbuffer uint8 crypto_publickeybytes) (h0 h1: HS.mem) = 
    live h0 pk /\ live h1 pk /\ modifies1 pk h0 h1 /\ equal_domains h0 h1

private let reveal_valid_pk (pk: lbuffer uint8 crypto_publickeybytes) (h0 h1: HS.mem) : 
    Lemma (ensures (valid_pk pk h0 h1) <==> (live h0 pk /\ live h1 pk /\ modifies1 pk h0 h1 /\ equal_domains h0 h1)) =
    reveal_opaque (`%valid_pk) valid_pk

private inline_for_extraction noextract
val encode_pk_ptSet:
    snapshot: HS.mem
  -> pk: lbuffer uint8 crypto_publickeybytes
  -> i: size_t
  -> j: size_t{v i + v j < v crypto_publickeybytes / (numbytes U32)}
  -> value: I32.t
  -> Unsafe unit // Despite the name of the effect, Nik assures us this is a correct use!
    (requires fun h -> valid_pk pk snapshot h)
    (ensures fun _ _ h1 -> valid_pk pk snapshot h1)

let encode_pk_ptSet snapshot pk i j value =
    let h0 = ST.get () in
    reveal_valid_pk pk snapshot h0;
    [@inline_let] let elem_to_uint32 x = Lib.RawIntTypes.u32_from_UInt32 (elem_to_uint32 x) in
    uint_to_bytes_le #U32 #_ (sub pk ((i +. j) *. size (numbytes U32)) (size (numbytes U32))) (elem_to_uint32 value);
    let h1 = ST.get () in
    reveal_valid_pk pk snapshot h1

[@"opaque_to_smt"]
private let valid_t (t: poly_k) (h0 h1: HS.mem) = live h0 t /\ live h1 t /\ h0 == h1

private let reveal_valid_t (t: poly_k) (h0 h1: HS.mem) :
    Lemma (ensures (valid_t t h0 h1) <==> (live h0 t /\ live h1 t /\ h0 == h1)) =
    reveal_opaque (`%valid_t) valid_t

private inline_for_extraction noextract
val encode_pk_tGet:
    snapshot: HS.mem
  -> t: poly_k
  -> j: size_t
  -> k: size_t{v j + v k < v params_n * v params_k}
  -> Unsafe (r:elem{is_pk r})
    (requires fun h -> valid_t t snapshot h /\ is_poly_k_pk h t)
    (ensures fun _ e h1 -> valid_t t snapshot h1 /\ is_poly_k_pk h1 t /\ e == bget h1 t (v j + v k))

let encode_pk_tGet snapshot t j k = 
    let h = ST.get () in
    reveal_valid_t t snapshot h;
    assert(is_poly_k_pk h t);
    assert(is_pk (bget h t (v j + v k)));
    t.(j +. k)

let valid_t_valid_pk (t:poly_k) (pk: lbuffer uint8 crypto_publickeybytes) (h0 h1:HS.mem)
  : Lemma (requires (valid_t t h0 h1 /\ live h0 pk))
          (ensures valid_pk pk h0 h1)
  = reveal_valid_t t h0 h1;
    reveal_valid_pk pk h0 h1

private inline_for_extraction noextract
val encode_pk_loopBody:
    pk: lbuffer uint8 crypto_publickeybytes
  -> t: poly_k
  -> i: size_t{v i + 22 < v crypto_publickeybytes / numbytes U32} 
  -> j: size_t{v j + 31 < v params_n}
  -> Stack unit
    (requires fun h -> live h pk /\ live h t /\ disjoint pk t /\ is_poly_k_pk h t)
    (ensures fun h0 _ h1 -> modifies1 pk h0 h1)

#reset-options "--z3rlimit 1000 --max_fuel 0 --max_ifuel 0 --query_stats \
                --z3cliopt 'smt.qi.eager_threshold=100'"

let encode_pk_loopBody pk t i j = 
    let h0 = ST.get () in
    reveal_valid_t t h0 h0;
    assert(valid_t t h0 h0);
    assert(is_poly_k_pk h0 t);
    [@inline_let] let tj = encode_pk_tGet h0 t in
    let tj0  = tj j (size 0)  in let tj1 = tj j (size 1)   in let tj2  = tj j (size 2)  in let tj3  = tj j (size 3) in 
    let tj4  = tj j (size 4)  in let tj5 = tj j (size 5)   in let tj6  = tj j (size 6)  in let tj7  = tj j (size 7) in
    let tj8  = tj j (size 8)  in let tj9 = tj j (size 9)   in let tj10 = tj j (size 10) in let tj11 = tj j (size 11) in 
    let tj12 = tj j (size 12) in let tj13 = tj j (size 13) in let tj14 = tj j (size 14) in let tj15 = tj j (size 15) in 
    let tj16 = tj j (size 16) in let tj17 = tj j (size 17) in let tj18 = tj j (size 18) in let tj19 = tj j (size 19) in 
    let tj20 = tj j (size 20) in let tj21 = tj j (size 21) in let tj22 = tj j (size 22) in let tj23 = tj j (size 23) in 
    let tj24 = tj j (size 24) in let tj25 = tj j (size 25) in let tj26 = tj j (size 26) in let tj27 = tj j (size 27) in 
    let tj28 = tj j (size 28) in let tj29 = tj j (size 29) in let tj30 = tj j (size 30) in let tj31 = tj j (size 31) in 
    let h1 = ST.get () in
    valid_t_valid_pk t pk h0 h1;
    // reveal_valid_t t h0 h1;a
    // assert(valid_t t h0 h1);

    // reveal_valid_pk pk h1 h1;
    // assert(valid_pk pk h1 h1);
    // In the reference code, "pt = (uint32_t*)pk" where pk is (unsigned char *). We can't recast buffers to have different
    // element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry encode_pk_ptSet above with pk as its first parameter to provide a function that looks a lot
    // like the integer assignment in the reference code, and it extracts down to store32_le in C.
    [@inline_let] let pt = encode_pk_ptSet h0 pk in
    [@inline_let] let op_Greater_Greater_Hat = op_Greater_Greater_Greater_Hat in
    [@inline_let] let op_Less_Less_Hat = op_Less_Less_Less_Hat in
    pt i (size 0)  (tj0              |^ (tj1  <<^ 23ul)); 
    pt i (size 1)  ((tj1  >>^ 9ul)   |^ (tj2  <<^ 14ul)); pt i (size 2)   ((tj2  >>^ 18ul)  |^ (tj3  <<^  5ul) |^ (tj4 <<^ 28ul)); 
    pt i (size 3)  ((tj4  >>^  4ul)  |^ (tj5  <<^ 19ul));
    pt i (size 4)  ((tj5  >>^ 13ul)  |^ (tj6  <<^ 10ul)); pt i (size 5)   ((tj6  >>^ 22ul)  |^ (tj7  <<^  1ul) |^ (tj8 <<^ 24ul));
    pt i (size 6)  ((tj8  >>^  8ul)  |^ (tj9  <<^ 15ul)); pt i (size 7)   ((tj9  >>^ 17ul)  |^ (tj10 <<^ 6ul) |^ (tj11 <<^ 29ul));
    pt i (size 8)  ((tj11 >>^  3ul)  |^ (tj12 <<^ 20ul));
    pt i (size 9)  ((tj12 >>^ 12ul)  |^ (tj13 <<^ 11ul)); pt i (size 10)  ((tj13 >>^ 21ul)  |^ (tj14 <<^  2ul) |^ (tj15 <<^ 25ul));
    pt i (size 11) ((tj15 >>^  7ul)  |^ (tj16 <<^ 16ul)); pt i (size 12)  ((tj16 >>^ 16ul)  |^ (tj17 <<^  7ul) |^ (tj18 <<^ 30ul));
    pt i (size 13) ((tj18 >>^  2ul)  |^ (tj19 <<^ 21ul));
    pt i (size 14) ((tj19 >>^ 11ul)  |^ (tj20 <<^ 12ul)); pt i (size 15)  ((tj20 >>^ 20ul)  |^ (tj21 <<^  3ul) |^ (tj22 <<^ 26ul));
    pt i (size 16) ((tj22 >>^  6ul)  |^ (tj23 <<^ 17ul)); pt i (size 17)  ((tj23 >>^ 15ul)  |^ (tj24 <<^  8ul) |^ (tj25 <<^ 31ul));
    pt i (size 18) ((tj25 >>^  1ul)  |^ (tj26 <<^ 22ul)); 
    pt i (size 19) ((tj26 >>^ 10ul)  |^ (tj27 <<^ 13ul)); pt i (size 20)  ((tj27 >>^ 19ul)  |^ (tj28 <<^  4ul) |^ (tj29 <<^ 27ul)); 
    pt i (size 21) ((tj29 >>^  5ul)  |^ (tj30 <<^ 18ul));
    pt i (size 22) ((tj30 >>^ 14ul)  |^ (tj31 <<^  9ul));
    let h2 = ST.get () in
    reveal_valid_pk pk h0 h2

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

//private let crypto_publickeybytes = (params_n *. params_q_log +. size 7) /. size 8 +. crypto_seedbytes

private let lemma_encode_pk_bound_i (k: size_t{v k < v params_n / 32}) : Lemma
    (ensures v k * v params_q_log + 22 < v crypto_publickeybytes / numbytes U32) = ()

val encode_pk:
    pk: lbuffer uint8 crypto_publickeybytes
  -> t: poly_k
  -> seedA: lbuffer uint8 crypto_seedbytes
  -> Stack unit
    (requires fun h -> live h pk /\ live h t /\ live h seedA /\
                    disjoint pk t /\ disjoint pk seedA /\ disjoint t seedA /\
                    is_poly_k_pk h t)
    (ensures fun h0 _ h1 -> modifies1 pk h0 h1)
(*    let looptest h = live h pk /\ live h t /\ live h i /\ live h j /\ modifies3 pk i j h0 h /\ is_poly_k_pk h t in
    while
    #(fun h -> looptest h)
    #(fun b h -> looptest h /\ 
              (b ==> (v (bget h j 0) + 31 < v params_n /\ v (bget h i 0) + 22 < v crypto_publickeybytes / numbytes U32)))*)

let encode_pk pk t seedA =
    let hInit = ST.get () in
    push_frame();

    let i = create (size 1) (size 0) in
    let j = create (size 1) (size 0) in

    assert(v params_k = 1);

    let h0 = ST.get () in
    assert(is_poly_k_equal hInit h0 t);
    assert(is_poly_k_pk h0 t);
    for 0ul (params_n /. size 32)
    (fun h k -> live h pk /\ live h t /\ modifies1 pk h0 h /\ is_poly_k_pk h t)
    (fun k ->
        let j = k *. size 32 in
        let i = k *. params_q_log in
        let h1 = ST.get () in
        // This assertion is necessary for bounds calculation to succeed for encode_pk_loopBody. Curiously, I have
        // to first prove this in terms of machine integers (k <. params_n /. size 32). Attempting to prove
        // (v k < v params_n / 32) fails, unless I assert the machine integer version first.
        assert(k <. params_n /. size 32);
        encode_pk_loopBody pk t i j
    );

    update_sub #MUT #_ #_ pk (params_n *. params_q_log /. size 8) crypto_seedbytes seedA;
    
    pop_frame()

// The prover gets overwhelmed if we give it lots of state to keep track of. This predicate and the "reveal" lemma
// below abstract underlying state away into this predicate, which the prover can chain through the loop body,
// and then only at the beginning and the end do we have to ask it to prove all these underlying stateful facts. The
// opaque_to_smt annotation allows us to choose when the solver digs into the predicate's definition.
[@"opaque_to_smt"]
private let valid_decode_pk (pk_in: lbuffer uint8 crypto_publickeybytes) (pk: lbuffer I32.t (params_n *. params_k)) (h0 h1: HS.mem) (i:size_t{v i + 31 < v params_n * v params_k}) = 
    live h0 pk_in /\ live h0 pk /\ live h1 pk_in /\ live h1 pk /\ modifies1 (gsub pk i (size 32)) h0 h1 /\ equal_domains h0 h1

private let reveal_valid_decode_pk (pk_in: lbuffer uint8 crypto_publickeybytes) (pk: lbuffer I32.t (params_n *. params_k)) (h0 h1: HS.mem) (i:size_t{v i + 31 < v params_n * v params_k}) : 
    Lemma (ensures (valid_decode_pk pk_in pk h0 h1 i) <==> 
                   (live h0 pk_in /\ live h0 pk /\ live h1 pk_in /\ live h1 pk /\ modifies1 (gsub pk i (size 32)) h0 h1 /\ equal_domains h0 h1)) =
    reveal_opaque (`%valid_decode_pk) valid_decode_pk

private inline_for_extraction noextract
val decode_pk_pt:
    snapshot : HS.mem
  -> pk : lbuffer I32.t (params_n *. params_k)
  -> pk_in : lbuffer uint8 crypto_publickeybytes
  -> i : size_t{v i + 31 < v params_n * v params_k}
  -> j : size_t
  -> k : size_t{v j + v k < v crypto_publickeybytes / 4}
  -> Stack UI32.t
    (requires fun h -> valid_decode_pk pk_in pk snapshot h i)
    (ensures fun h0 _ h1 -> h0 == h1 /\ valid_decode_pk pk_in pk snapshot h1 i)

let decode_pk_pt snapshot pk pk_in i j k =
    let h0 = ST.get () in
    reveal_valid_decode_pk pk_in pk snapshot h0 i;
    assert(live h0 pk_in);
    let u = uint_from_bytes_le #U32 #_ (sub pk_in ((j +. k) *. size (numbytes U32)) (size (numbytes U32))) in
    Lib.RawIntTypes.u32_to_UInt32 u

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

private inline_for_extraction noextract
val decode_pk_set_pk:
    snapshot : HS.mem
  -> pk_in : lbuffer uint8 crypto_publickeybytes
  -> pk : lbuffer I32.t (params_n *. params_k)
  -> i : size_t{v i + 31 < v params_n * v params_k}
  -> j : size_t{v j < 32} // {v i + v j < v params_n * v params_k}
  -> value : I32.t
  -> Unsafe unit
    (requires fun h -> valid_decode_pk pk_in pk snapshot h i)
    (ensures fun _ _ h1 -> valid_decode_pk pk_in pk snapshot h1 i /\ (bget h1 pk (v i + v j)) = value)

let decode_pk_set_pk snapshot pk_in pk i j value =
    let h0 = ST.get () in
    reveal_valid_decode_pk pk_in pk snapshot h0 i;
    // We used to just have "modifies1 pk h0 h1" as the post-condition for this function, but this messes us up
    // at the top level because we need to use the fact that in each loop of decode_pk_loopBody, all elements of pk
    // before index i are unchanged. We need "modifies1 (gsub pk i (size 32)) h0 h1" to prove this. We used to
    // set this element with "pk.(i +. j) <- value", but the prover has issues bridging the gap between this and the
    // subbuffer.
    //let subPk = sub pk i (size 32) in
    //subPk.(j) <- value;
    pk.(i +. j) <- value;
    let h1 = ST.get () in
    assert(j <. size 32);
    assert(B.get h1 (pk <: B.buffer elem) (v i + v j) == B.get h1 (B.gsub (pk <: B.buffer elem) i (size 32)) (v j));
    assert(forall (k:nat{k < 32}) (h:HS.mem) . {:pattern bget h pk (v i + k) \/ bget h (gsub pk i (size 32)) k} bget h pk (v i + k) == bget h (gsub pk i (size 32)) k);
    reveal_valid_decode_pk pk_in pk snapshot h1 i;
    assume(modifies1 (gsub pk i (size 32)) h0 h1)

private let lemma_decode_pk_extend 
    (pk : lbuffer I32.t (params_n *. params_k))
    (i : size_t{v i + 31 < v params_n * v params_k})
    (h : HS.mem) : Lemma
    (requires is_poly_k_pk_i h pk (v i) /\
              (forall (k:nat{k >= v i /\ k < v i + 32}) . is_pk (bget h pk k)))
    (ensures is_poly_pk_i h pk (v i + 32)) = ()

private inline_for_extraction noextract
val decode_pk_loopBody:
    pk : lbuffer I32.t (params_n *. params_k)
  -> pk_in : lbuffer uint8 crypto_publickeybytes
  -> mask23 : UI32.t{UI32.v mask23 == UI32.v UI32.(1ul <<^ params_q_log) - 1}
  -> i : size_t{v i + 31 < v params_n * v params_k}
  -> j : size_t{v j + 22 < v crypto_publickeybytes / 4}
  -> Stack unit
    (requires fun h -> live h pk /\ live h pk_in /\ disjoint pk pk_in /\ is_poly_k_pk_i h pk (v i))
    (ensures fun h0 _ h1 -> modifies1 pk h0 h1 /\ is_poly_k_pk_i h1 pk (v i + 32))

#push-options "--z3rlimit 800"
let decode_pk_loopBody pk pk_in mask23 i j =
    let h0 = ST.get () in
    reveal_valid_decode_pk pk_in pk h0 h0 i;
    assert(modifies1 (gsub pk i (size 32)) h0 h0); 
    assert(valid_decode_pk pk_in pk h0 h0 i);

    // In the reference code, "pt = (uint32_t*)pk_in" where pk_in is (unsigned char *). We can't recast buffers to have
    // different element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry decode_pk_pt above with pk_in as its first parameter to provide a function that looks a lot
    // like the array dereference in the reference code, and extracts down to load32_le.
    [@inline_let] let pt = decode_pk_pt h0 pk pk_in i in

    // Helper function to set elements of pk just to spread the work of the prover out.
    assert(v i < v (params_n *. params_k));
    [@inline_let] let pks = decode_pk_set_pk h0 pk_in pk in

    // Doing these statements in the form of "pk.(i+.size #) <- UI32.(expression)" causes typechecking problems.
    // Lifting the calculation into a let of time UI32.t and then passing it to uint32_to_int32 works at the
    // expense of junking up the code.
    [@inline_let] let u2i = uint32_to_int32 in

    // In the reference code, assignment is done to pp, and "pp = (uint32_t*)pk". Here instead we inline the
    // cast of the reuslt from uint32_t to int32_t in each assignment and then assign directly to elements of pk.
    let ppi = UI32.( (pt j (size 0)) &^ mask23 ) in pks i (size 0) (u2i ppi);
    let ppi1 = UI32.( (((pt j (size  0)) >>^ 23ul) |^ ((pt j (size  1))) <<^  9ul) &^ mask23 ) in pks i (size 1) (u2i ppi1);
    let ppi2 = UI32.( (((pt j (size  1)) >>^ 14ul) |^ ((pt j (size  2))) <<^ 18ul) &^ mask23 ) in pks i (size 2) (u2i ppi2);
    let ppi3 = UI32.(  ((pt j (size  2)) >>^  5ul) &^ mask23 ) in pks i (size  3) (u2i ppi3);
    let ppi4 = UI32.( (((pt j (size  2)) >>^ 28ul) |^ ((pt j (size  3))) <<^  4ul) &^ mask23 ) in pks i (size  4) (u2i ppi4);
    let ppi5 = UI32.( (((pt j (size  3)) >>^ 19ul) |^ ((pt j (size  4))) <<^ 13ul) &^ mask23 ) in pks i (size  5) (u2i ppi5);
    let ppi6 = UI32.( (((pt j (size  4)) >>^ 10ul) |^ ((pt j (size  5))) <<^ 22ul) &^ mask23 ) in pks i (size  6) (u2i ppi6);
    let ppi7 = UI32.(  ((pt j (size  5)) >>^  1ul) &^ mask23 ) in pks i (size  7) (u2i ppi7);
    let ppi8 = UI32.( (((pt j (size  5)) >>^ 24ul) |^ ((pt j (size  6))) <<^  8ul) &^ mask23 ) in pks i (size  8) (u2i ppi8);
    let ppi9 = UI32.( (((pt j (size  6)) >>^ 15ul) |^ ((pt j (size  7))) <<^ 17ul) &^ mask23 ) in pks i (size  9) (u2i ppi9);
    let ppi10 = UI32.(  ((pt j (size  7)) >>^  6ul) &^ mask23 ) in pks i (size 10)  (u2i ppi10);
    let ppi11 = UI32.( (((pt j (size  7)) >>^ 29ul) |^ ((pt j (size  8))) <<^  3ul) &^  mask23 ) in pks i (size 11) (u2i ppi11);
    let ppi12 = UI32.( (((pt j (size  8)) >>^ 20ul) |^ ((pt j (size  9))) <<^ 12ul) &^ mask23 ) in pks i (size 12) (u2i ppi12);
    let ppi13 = UI32.( (((pt j (size  9)) >>^ 11ul) |^ ((pt j (size 10))) <<^ 21ul) &^ mask23 ) in pks i (size 13) (u2i ppi13);
    let ppi14 = UI32.(  ((pt j (size 10)) >>^  2ul) &^ mask23 ) in pks i (size 14) (u2i ppi14);
    let ppi15 = UI32.( (((pt j (size 10)) >>^ 25ul) |^ ((pt j (size 11))) <<^  7ul) &^ mask23 ) in pks i (size 15) (u2i ppi15);
    let ppi16 = UI32.( (((pt j (size 11)) >>^ 16ul) |^ ((pt j (size 12))) <<^ 16ul) &^ mask23 ) in pks i (size 16) (u2i ppi16);
    let ppi17 = UI32.(  ((pt j (size 12)) >>^  7ul) &^ mask23 ) in pks i (size 17) (u2i ppi17);
    let ppi18 = UI32.( (((pt j (size 12)) >>^ 30ul) |^ ((pt j (size 13))) <<^  2ul) &^ mask23 ) in pks i (size 18) (u2i ppi18);
    let ppi19 = UI32.( (((pt j (size 13)) >>^ 21ul) |^ ((pt j (size 14))) <<^ 11ul) &^ mask23 ) in pks i (size 19) (u2i ppi19);
    let ppi20 = UI32.( (((pt j (size 14)) >>^ 12ul) |^ ((pt j (size 15))) <<^ 20ul) &^ mask23 ) in pks i (size 20) (u2i ppi20);
    let ppi21 = UI32.(  ((pt j (size 15)) >>^  3ul) &^ mask23 ) in pks i (size 21) (u2i ppi21);
    let ppi22 = UI32.( (((pt j (size 15)) >>^ 26ul) |^ ((pt j (size 16))) <<^  6ul) &^ mask23 ) in pks i (size 22) (u2i ppi22);
    let ppi23 = UI32.( (((pt j (size 16)) >>^ 17ul) |^ ((pt j (size 17))) <<^ 15ul) &^ mask23 ) in pks i (size 23) (u2i ppi23);
    let ppi24 = UI32.(  ((pt j (size 17)) >>^  8ul) &^ mask23 ) in pks i (size 24) (u2i ppi24);
    let ppi25 = UI32.( (((pt j (size 17)) >>^ 31ul) |^ ((pt j (size 18))) <<^  1ul) &^ mask23 ) in pks i (size 25) (u2i ppi25);
    let ppi26 = UI32.( (((pt j (size 18)) >>^ 22ul) |^ ((pt j (size 19))) <<^ 10ul) &^ mask23 ) in pks i (size 26) (u2i ppi26);
    let ppi27 = UI32.( (((pt j (size 19)) >>^ 13ul) |^ ((pt j (size 20))) <<^ 19ul) &^ mask23 ) in pks i (size 27) (u2i ppi27);
    let ppi28 = UI32.(  ((pt j (size 20)) >>^  4ul) &^ mask23 ) in pks i (size 28) (u2i ppi28);
    let ppi29 = UI32.( (((pt j (size 20)) >>^ 27ul) |^ ((pt j (size 21))) <<^  5ul) &^ mask23 ) in pks i (size 29) (u2i ppi29);
    let ppi30 = UI32.( (((pt j (size 21)) >>^ 18ul) |^ ((pt j (size 22))) <<^ 14ul) &^ mask23 ) in pks i (size 30) (u2i ppi30);
    let ppi31 = UI32.( (pt j (size 22)) >>^  9ul ) in pks i (size 31) (u2i ppi31);

    let h1 = ST.get () in
    reveal_valid_decode_pk pk_in pk h0 h1 i;
    assert(valid_decode_pk pk_in pk h0 h1 i);
    // Can't easily prove is_pk for all k < i because we need to articulate somehow that the above
    // sets don't modify those parts of the buffer.
    assert(modifies1 (gsub pk i (size 32)) h0 h1);
    //assume(v i > 0);
    //assert(disjoint (gsub pk (size 0) i) (gsub pk i (size 32)));
    //assert(forall (k:nat{k < v i}) . B.get h0 ((gsub pk (size 0) i) <: B.buffer elem) k == B.get h1 ((gsub pk (size 0) i) <: B.buffer elem) k);
    assert(forall (k:nat{k < v i}) . bget h0 (gsub pk (size 0) i) k == bget h1 (gsub pk (size 0) i) k);
    assume(forall (k:nat{k >= v i /\ k < v i + 32}) . is_pk (bget h1 pk k));
    // index reassignment assertion
    assert(forall (k:nat{k < v i}) (h:HS.mem) . {:pattern bget h pk k \/ bget h (gsub pk (size 0) i) k} bget h pk k == bget h (gsub pk (size 0) i) k);
    assert(is_poly_k_pk_i h1 pk (v i));
    lemma_decode_pk_extend pk i h1
#pop-options

#push-options "--max_fuel 0"
private let let_mask23_left_minus_1_fits () : Lemma
    (ensures UInt.fits (UI32.v UI32.(1ul <<^ params_q_log) - 1) UI32.n) = 
    UInt.shift_left_value_lemma #UI32.n 1 (v params_q_log);
    normalize_term_spec (pow2 params_q_log_int)
#pop-options

val decode_pk:
    pk : lbuffer I32.t (params_n *. params_k)
  -> seedA : lbuffer uint8 crypto_seedbytes
  -> pk_in : lbuffer uint8 crypto_publickeybytes
  -> Stack unit
    (requires fun h -> live h pk /\ live h seedA /\ live h pk_in /\ disjoint pk seedA /\ disjoint pk pk_in /\ disjoint seedA pk_in)
    (ensures fun h0 _ h1 -> modifies2 pk seedA h0 h1 /\ is_poly_k_pk h1 pk)

let decode_pk pk seedA pk_in =
    //let iBuf = create (size 1) (size 0) in
    //let jBuf = create (size 1) (size 0) in
    // In the reference implementation, pp is a uint32_t view into pk. We can't do that in F*, so we operate
    // directly on pk, doing a cast from int32 to uint32 in-line. pt is a uint32_t view into pk, and the
    // function pt above takes care of doing that conversion.
    let mask23_left:UI32.t = UI32.(1ul <<^ params_q_log) in
    let_mask23_left_minus_1_fits ();
    let mask23:UI32.t = UI32.(mask23_left -^ 1ul) in

    let h0 = ST.get () in
    for (size 0) (params_n /. size 32)
    (fun h k -> live h pk /\ live h pk_in /\ modifies1 pk h0 h /\ k <= v params_n / 32 /\ is_poly_k_pk_i h pk (k * 32))
    (fun k ->
        let j = k *. size 23 in
        let i = k *. size 32 in
        assert(v k < v (params_n /. size 32)); // Refinement on i fails to prove without this.
        decode_pk_loopBody pk pk_in mask23 i j
    );

    // Actually have to point this fact out to the prover to prove the post-condition.
    let h1 = ST.get () in
    assert(is_poly_k_pk_i h1 pk (v (params_n /. size 32) * 32));

    assert(v params_k = 1);
    copy seedA (sub pk_in (params_n *. params_q_log /. size 8) crypto_seedbytes)

[@"opaque_to_smt"]
private let valid_encode_sig (z: poly) (sm: lbuffer uint8 crypto_bytes) (h0 h1: HS.mem) =
    live h0 z /\ live h0 sm /\ live h1 z /\ live h1 sm /\ modifies1 sm h0 h1 /\ equal_domains h0 h1

private let reveal_valid_encode_sig (z: poly) (sm: lbuffer uint8 crypto_bytes) (h0 h1: HS.mem) :
    Lemma (ensures (valid_encode_sig z sm h0 h1) <==> 
                   (live h0 z /\ live h0 sm /\ live h1 z /\ live h1 sm /\ modifies1 sm h0 h1 /\ equal_domains h0 h1)) =
    reveal_opaque (`%valid_encode_sig) valid_encode_sig

// Set an element of an unsigned char array as if it were a uint32
private inline_for_extraction noextract
val encode_sig_ptSet:
    snapshot : HS.mem
  -> z : poly
  -> sm : lbuffer uint8 crypto_bytes
  -> i : size_t
  -> k : size_t{v i + v k < v crypto_bytes / 4}
  -> value : UI32.t
  -> Unsafe unit
    (requires fun h -> valid_encode_sig z sm snapshot h)
    (ensures fun _ _ h1 -> valid_encode_sig z sm snapshot h1)

let encode_sig_ptSet snapshot z sm i k value = 
    let h0 = ST.get () in
    reveal_valid_encode_sig z sm snapshot h0;
    assert(live h0 sm);
    [@inline_let] let valueAsUint = Lib.RawIntTypes.u32_from_UInt32 value in
    uint_to_bytes_le #U32 #_ (sub sm ((i +. k) *. size (numbytes U32)) (size (numbytes U32))) valueAsUint;
    let h1 = ST.get () in
    reveal_valid_encode_sig z sm snapshot h1

private inline_for_extraction noextract
val encode_sig_tGet:
    snapshot : HS.mem
  -> sm : lbuffer uint8 crypto_bytes
  -> z : poly
  -> j : size_t
  -> k : size_t{v j + v k < v params_n * v params_k}
  -> Unsafe UI32.t
    (requires fun h -> valid_encode_sig z sm snapshot h)
    (ensures fun h0 _ h1 -> (*h0 == h1 /\*) valid_encode_sig z sm snapshot h1)
    // Including h0 == h1 in the postcondition somehow makes encode_sig_loopBody checking time out

let encode_sig_tGet snapshot sm z j k = 
    let h0 = ST.get () in
    reveal_valid_encode_sig z sm snapshot h0;
    let zj = z.(j +. k) in elem_to_uint32 zj

private inline_for_extraction noextract
val encode_sig_loopBody:
    sm : lbuffer uint8 crypto_bytes
  -> z : poly
  -> k : size_t{v k < v params_n / 32}
  -> Stack unit
    (requires fun h -> live h sm /\ live h z /\ disjoint sm z)
    (ensures fun h0 _ h1 -> modifies1 sm h0 h1)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

let encode_sig_loopBody sm z k =
    let i = k *. params_d in
    let j = k *. size 32 in

    let h0 = ST.get () in
    // Can't use t for this definition, because t is defined in UI64 as a type and overrides this definition when we
    // qualify the below expressions in the UI64 module's namespace.
    [@inline_let] let t_ = encode_sig_tGet h0 sm z in
    [@inline_let] let pt = encode_sig_ptSet h0 z sm in

    reveal_valid_encode_sig z sm h0 h0;
    assert(valid_encode_sig z sm h0 h0);

    pt i (size  0)  UI32.( ((t_ j (size  0))           &^ ((1ul <<^ 21ul) -^ 1ul)) |^ ((t_ j (size  1)) <<^ 21ul) );
    pt i (size  1) UI32.( (((t_ j (size  1)) >>^ 11ul) &^ ((1ul <<^ 10ul) -^ 1ul)) |^ (((t_ j (size  2)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^ 10ul) |^ ((t_ j (size  3)) <<^ 31ul) );
    pt i (size  2) UI32.( (((t_ j (size  3)) >>^  1ul) &^ ((1ul <<^ 20ul) -^ 1ul)) |^ ((t_ j (size  4)) <<^ 20ul) );
    pt i (size  3) UI32.( (((t_ j (size  4)) >>^ 12ul) &^ ((1ul <<^  9ul) -^ 1ul)) |^ (((t_ j (size  5)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  9ul) |^ ((t_ j (size  6)) <<^ 30ul) );
    pt i (size  4) UI32.( (((t_ j (size  6)) >>^  2ul) &^ ((1ul <<^ 19ul) -^ 1ul)) |^ ((t_ j (size  7)) <<^ 19ul) );
    pt i (size  5) UI32.( (((t_ j (size  7)) >>^ 13ul) &^ ((1ul <<^  8ul) -^ 1ul)) |^ (((t_ j (size  8)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  8ul) |^ ((t_ j (size  9)) <<^ 29ul) );
    pt i (size  6) UI32.( (((t_ j (size  9)) >>^  3ul) &^ ((1ul <<^ 18ul) -^ 1ul)) |^ ((t_ j (size 10)) <<^ 18ul) );
    pt i (size  7) UI32.( (((t_ j (size 10)) >>^ 14ul) &^ ((1ul <<^  7ul) -^ 1ul)) |^ (((t_ j (size 11)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  7ul) |^ ((t_ j (size 12)) <<^ 28ul) );
    pt i (size  8) UI32.( (((t_ j (size 12)) >>^  4ul) &^ ((1ul <<^ 17ul) -^ 1ul)) |^ ((t_ j (size 13)) <<^ 17ul) );
    pt i (size  9) UI32.( (((t_ j (size 13)) >>^ 15ul) &^ ((1ul <<^  6ul) -^ 1ul)) |^ (((t_ j (size 14)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  6ul) |^ ((t_ j (size 15)) <<^ 27ul) );
    pt i (size 10) UI32.( (((t_ j (size 15)) >>^  5ul) &^ ((1ul <<^ 16ul) -^ 1ul)) |^ ((t_ j (size 16)) <<^ 16ul) );
    pt i (size 11) UI32.( (((t_ j (size 16)) >>^ 16ul) &^ ((1ul <<^  5ul) -^ 1ul)) |^ (((t_ j (size 17)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  5ul) |^ ((t_ j (size 18)) <<^ 26ul) );
    pt i (size 12) UI32.( (((t_ j (size 18)) >>^  6ul) &^ ((1ul <<^ 15ul) -^ 1ul)) |^ ((t_ j (size 19)) <<^ 15ul) );
    pt i (size 13) UI32.( (((t_ j (size 19)) >>^ 17ul) &^ ((1ul <<^  4ul) -^ 1ul)) |^ (((t_ j (size 20)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  4ul) |^ ((t_ j (size 21)) <<^ 25ul) );
    pt i (size 14) UI32.( (((t_ j (size 21)) >>^  7ul) &^ ((1ul <<^ 14ul) -^ 1ul)) |^ ((t_ j (size 22)) <<^ 14ul) );
    pt i (size 15) UI32.( (((t_ j (size 22)) >>^ 18ul) &^ ((1ul <<^  3ul) -^ 1ul)) |^ (((t_ j (size 23)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  3ul) |^ ((t_ j (size 24)) <<^ 24ul) );
    pt i (size 16) UI32.( (((t_ j (size 24)) >>^  8ul) &^ ((1ul <<^ 13ul) -^ 1ul)) |^ ((t_ j (size 25)) <<^ 13ul) );
    pt i (size 17) UI32.( (((t_ j (size 25)) >>^ 19ul) &^ ((1ul <<^  2ul) -^ 1ul)) |^ (((t_ j (size 26)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  2ul) |^ ((t_ j (size 27)) <<^ 23ul) );
    pt i (size 18) UI32.( (((t_ j (size 27)) >>^  9ul) &^ ((1ul <<^ 12ul) -^ 1ul)) |^ ((t_ j (size 28)) <<^ 12ul) );
    pt i (size 19) UI32.( (((t_ j (size 28)) >>^ 20ul) &^ ((1ul <<^  1ul) -^ 1ul)) |^ (((t_ j (size 29)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  1ul) |^ ((t_ j (size 30)) <<^ 22ul) );
    pt i (size 20) UI32.( (((t_ j (size 30)) >>^ 10ul) &^ ((1ul <<^ 11ul) -^ 1ul)) |^ ((t_ j (size 31)) <<^ 11ul) );

    let h1 = ST.get () in
    reveal_valid_encode_sig z sm h0 h1;
    assert(valid_encode_sig z sm h0 h1)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val encode_sig:
    sm : lbuffer uint8 crypto_bytes
  -> c : lbuffer uint8 crypto_c_bytes
  -> z : poly
  -> Stack unit
    (requires fun h -> live h sm /\ live h c /\ live h z /\ disjoint sm c /\ disjoint sm z /\ disjoint c z)
    (ensures fun h0 _ h1 -> modifies1 sm h0 h1)

let encode_sig sm c z =
    let h0 = ST.get () in
    for (size 0) (params_n /. size 32)
    (fun h _ -> live h sm /\ live h z /\ modifies1 sm h0 h)
    (fun k -> 
        assert(v k < v (params_n /. size 32));
        encode_sig_loopBody sm z k
    );

    update_sub #MUT #_ #_ sm (params_n *. params_d /. size 8) crypto_c_bytes c

[@"opaque_to_smt"]
private let valid_decode_sig (z: poly) (sm: lbuffer uint8 crypto_bytes) (h0 h1: HS.mem) =
    live h0 z /\ live h0 sm /\ live h1 z /\ live h1 sm /\ modifies1 z h0 h1 /\ equal_domains h0 h1

private let reveal_valid_decode_sig (z: poly) (sm: lbuffer uint8 crypto_bytes) (h0 h1: HS.mem) :
    Lemma (ensures (valid_decode_sig z sm h0 h1) <==>
                   (live h0 z /\ live h0 sm /\ live h1 z /\ live h1 sm /\ modifies1 z h0 h1 /\ equal_domains h0 h1)) =
    reveal_opaque (`%valid_decode_sig) valid_decode_sig

private inline_for_extraction noextract
val decode_sig_pt:
    snapshot : HS.mem
  -> z : poly
  -> sm : lbuffer uint8 crypto_bytes
  -> j : size_t
  -> k : size_t{v j + v k < v crypto_bytes / 4}
  -> Unsafe UI32.t
    (requires fun h -> valid_decode_sig z sm snapshot h)
    (ensures fun _ _ h1 -> valid_decode_sig z sm snapshot h1)

let decode_sig_pt snapshot z sm j k =
    let h0 = ST.get () in
    reveal_valid_decode_sig z sm snapshot h0;
    assert(valid_decode_sig z sm snapshot h0); 
    let u = uint_from_bytes_le #U32 #_ (sub sm ((j +. k) *. (size (numbytes U32))) (size (numbytes U32))) in
    Lib.RawIntTypes.u32_to_UInt32 u

private inline_for_extraction noextract
val decode_sig_setz:
    snapshot : HS.mem
  -> sm : lbuffer uint8 crypto_bytes
  -> z : poly
  -> i : size_t
  -> k : size_t{v i + v k < v params_n * v params_k}
  -> value : I32.t // TODO: should be elem
  -> Unsafe unit
    (requires fun h -> valid_decode_sig z sm snapshot h)
    (ensures fun _ _ h1 -> valid_decode_sig z sm snapshot h1)

let decode_sig_setz snapshot sm z i k value =
    let h0 = ST.get () in
    reveal_valid_decode_sig z sm snapshot h0;
    assert(valid_decode_sig z sm snapshot h0);
    z.(i +. k) <- value;
    let h1 = ST.get () in
    reveal_valid_decode_sig z sm snapshot h1;
    assert(valid_decode_sig z sm snapshot h1)

private inline_for_extraction noextract
val decode_sig_loopBody:
    sm : lbuffer uint8 crypto_bytes
  -> z : poly
  -> k : size_t{v k < v params_n / 32}
  -> Stack unit
    (requires fun h -> live h sm /\ live h z /\ disjoint sm z)
    (ensures fun h0 _ h1 -> modifies1 z h0 h1)

#reset-options "--z3rlimit 800 --max_fuel 0 --max_ifuel 0"

let decode_sig_loopBody sm z k =
    let h0 = ST.get () in
    // In the reference code, "pt = (uint32_t*)sm" where sm is (unsigned char *). We can't recast buffers to have
    // different element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry decode_sig_pt above with smlen and sm as its two parameters to provide a function that looks a lot
    // like the array dereference in the reference code, and extracts down to load32_le.
    [@inline_let] let pt = decode_sig_pt h0 z sm in
    [@inline_let] let z_ = decode_sig_setz h0 sm z in
    [@inline_let] let u2i = uint32_to_int32 in
    [@inline_let] let i2e = int32_to_elem in

    reveal_valid_decode_sig z sm h0 h0;
    assert(valid_decode_sig z sm h0 h0);

    let j = k *. size 21 in

    // As above, putting a call to (pt j) inline in these computation causes a typechecking error. Instead we
    // let-bind all the elements of pt we will be working with and use those values in-line.
    let ptj0  = pt j (size  0) in    let ptj1  = pt j (size  1) in
    let ptj2  = pt j (size  2) in    let ptj3  = pt j (size  3) in
    let ptj4  = pt j (size  4) in    let ptj5  = pt j (size  5) in
    let ptj6  = pt j (size  6) in    let ptj7  = pt j (size  7) in
    let ptj8  = pt j (size  8) in    let ptj9  = pt j (size  9) in
    let ptj10 = pt j (size 10) in    let ptj11 = pt j (size 11) in
    let ptj12 = pt j (size 12) in    let ptj13 = pt j (size 13) in
    let ptj14 = pt j (size 14) in    let ptj15 = pt j (size 15) in
    let ptj16 = pt j (size 16) in    let ptj17 = pt j (size 17) in
    let ptj18 = pt j (size 18) in    let ptj19 = pt j (size 19) in
    let ptj20 = pt j (size 20) in

    let i = k *. size 32 in

    z_ i (size  0) (i2e I32.( u2i UI32.( ptj0 <<^ 11ul ) >>>^ 11ul ));
    z_ i (size  1) (i2e I32.( u2i UI32.( ptj0 >>^ 21ul ) |^ (u2i UI32.(ptj1 <<^ 22ul)) >>>^ 11ul ));
    z_ i (size  2) (i2e I32.( u2i UI32.( ptj1 <<^  1ul ) >>>^ 11ul ));
    z_ i (size  3) (i2e I32.( u2i UI32.( ptj1 >>^ 31ul ) |^ (u2i UI32.(ptj2 <<^ 12ul)) >>>^ 11ul ));
    z_ i (size  4) (i2e I32.( u2i UI32.( ptj2 >>^ 20ul ) |^ (u2i UI32.(ptj3 <<^ 23ul)) >>>^ 11ul ));
    z_ i (size  5) (i2e I32.( u2i UI32.( ptj3 <<^  2ul ) >>>^ 11ul ));
    z_ i (size  6) (i2e I32.( u2i UI32.( ptj3 >>^ 30ul ) |^ (u2i UI32.(ptj4 <<^ 13ul)) >>>^ 11ul ));
    z_ i (size  7) (i2e I32.( u2i UI32.( ptj4 >>^ 19ul ) |^ (u2i UI32.(ptj5 <<^ 24ul)) >>>^ 11ul ));
    z_ i (size  8) (i2e I32.( u2i UI32.( ptj5 <<^  3ul ) >>>^ 11ul ));
    z_ i (size  9) (i2e I32.( u2i UI32.( ptj5 >>^ 29ul ) |^ (u2i UI32.(ptj6 <<^ 14ul)) >>>^ 11ul ));
    z_ i (size 10) (i2e I32.( u2i UI32.( ptj6 >>^ 18ul ) |^ (u2i UI32.(ptj7 <<^ 25ul)) >>>^ 11ul ));
    z_ i (size 11) (i2e I32.( u2i UI32.( ptj7 <<^  4ul ) >>>^ 11ul ));
    z_ i (size 12) (i2e I32.( u2i UI32.( ptj7 >>^ 28ul ) |^ (u2i UI32.(ptj8 <<^ 15ul)) >>>^ 11ul ));
    z_ i (size 13) (i2e I32.( u2i UI32.( ptj8 >>^ 17ul ) |^ (u2i UI32.(ptj9 <<^ 26ul)) >>>^ 11ul ));
    z_ i (size 14) (i2e I32.( u2i UI32.( ptj9 <<^  5ul ) >>>^ 11ul ));
    z_ i (size 15) (i2e I32.( u2i UI32.( ptj9 >>^ 27ul ) |^ (u2i UI32.(ptj10 <<^ 16ul)) >>>^ 11ul ));
    z_ i (size 16) (i2e I32.( u2i UI32.( ptj10 >>^ 16ul ) |^ (u2i UI32.(ptj11 <<^ 27ul)) >>>^ 11ul ));
    z_ i (size 17) (i2e I32.( u2i UI32.( ptj11 <<^  6ul ) >>>^ 11ul ));
    z_ i (size 18) (i2e I32.( u2i UI32.( ptj11 >>^ 26ul ) |^ (u2i UI32.(ptj12 <<^ 17ul)) >>>^ 11ul ));
    z_ i (size 19) (i2e I32.( u2i UI32.( ptj12 >>^ 15ul ) |^ (u2i UI32.(ptj13 <<^ 28ul)) >>>^ 11ul ));
    z_ i (size 20) (i2e I32.( u2i UI32.( ptj13 <<^  7ul ) >>>^ 11ul ));
    z_ i (size 21) (i2e I32.( u2i UI32.( ptj13 >>^ 25ul ) |^ (u2i UI32.(ptj14 <<^ 18ul)) >>>^ 11ul ));
    z_ i (size 22) (i2e I32.( u2i UI32.( ptj14 >>^ 14ul ) |^ (u2i UI32.(ptj15 <<^ 29ul)) >>>^ 11ul ));
    z_ i (size 23) (i2e I32.( u2i UI32.( ptj15 <<^  8ul ) >>>^ 11ul ));
    z_ i (size 24) (i2e I32.( u2i UI32.( ptj15 >>^ 24ul ) |^ (u2i UI32.(ptj16 <<^ 19ul)) >>>^ 11ul ));
    z_ i (size 25) (i2e I32.( u2i UI32.( ptj16 >>^ 13ul ) |^ (u2i UI32.(ptj17 <<^ 30ul)) >>>^ 11ul ));
    z_ i (size 26) (i2e I32.( u2i UI32.( ptj17 <<^  9ul ) >>>^ 11ul ));
    z_ i (size 27) (i2e I32.( u2i UI32.( ptj17 >>^ 23ul ) |^ (u2i UI32.(ptj18 <<^ 20ul)) >>>^ 11ul ));
    z_ i (size 28) (i2e I32.( u2i UI32.( ptj18 >>^ 12ul ) |^ (u2i UI32.(ptj19 <<^ 31ul)) >>>^ 11ul ));
    z_ i (size 29) (i2e I32.( u2i UI32.( ptj19 <<^ 10ul ) >>>^ 11ul ));
    z_ i (size 30) (i2e I32.( u2i UI32.( ptj19 >>^ 22ul ) |^ (u2i UI32.(ptj20 <<^ 21ul)) >>>^ 11ul ));
    z_ i (size 31) (i2e I32.( u2i ptj20 >>>^ 11ul ));

    let h1 = ST.get () in
    reveal_valid_decode_sig z sm h0 h1;
    assert(valid_decode_sig z sm h0 h1)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val decode_sig:
    c: lbuffer uint8 crypto_c_bytes
  -> z: poly
  -> sm: lbuffer uint8 crypto_bytes
  -> Stack unit
    (requires fun h -> live h c /\ live h z /\ live h sm /\ disjoint c z /\ disjoint c sm /\ disjoint z sm)
    (ensures fun h0 _ h1 -> modifies2 c z h0 h1)

let decode_sig c z sm =
    let h0 = ST.get () in
    for (size 0) (params_n /. size 32)
    (fun h _ -> live h z /\ live h sm /\ modifies1 z h0 h)
    (fun k ->
        assert(v k < v (params_n /. size 32));
        decode_sig_loopBody sm z k);

    copy c (sub sm (params_n *. params_d /. size 8) crypto_c_bytes)
