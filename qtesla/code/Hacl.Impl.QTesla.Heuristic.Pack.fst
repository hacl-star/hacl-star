module Hacl.Impl.QTesla.Heuristic.Pack

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

// qTESLA-I and qTESLA-III-size share the implementation for: encode_pk decode_pk encode_sig decode_sig

private inline_for_extraction noextract
val encode_pk_ptSet:
    pk : lbuffer uint8 crypto_publickeybytes
  -> i : size_t{i <. crypto_publickeybytes /. (size UI32.n /. size 8)}
  -> value : elem
  -> Stack unit
    (requires fun h -> live h pk)
    (ensures fun h0 _ h1 -> modifies1 pk h0 h1)

let encode_pk_ptSet pk i value =
    uint_to_bytes_le #U32 #_ (sub pk (i *. size UI32.n /. size 8) (size UI32.n /. size 8)) (elem_to_uint32 value)

val encode_pk:
    pk: lbuffer uint8 crypto_publickeybytes
  -> t: poly_k
  -> seedA: lbuffer uint8 crypto_seedbytes
  -> Stack unit
    (requires fun h -> live h pk /\ live h t /\ live h seedA /\
                    disjoint pk t /\ disjoint pk seedA /\ disjoint t seedA)
    (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1)

let encode_pk pk t seedA =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in

    // In the reference code, "pt = (uint32_t*)pk" where pk is (unsigned char *). We can't recast buffers to have different
    // element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry encode_pk_ptSet above with pk as its first parameter to provide a function that looks a lot
    // like the integer assignment in the reference code, and it extracts down to store32_le in C.
    [@inline_let] let pt = encode_pk_ptSet pk in

    assert(v params_k = 1);
    
    while
    #(fun h -> live h t /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h t /\ live h iBuf /\ live h jBuf)
    (fun _ -> (iBuf.(size 0)) <. params_n *. params_q_log /. size 32)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in

        // I can't think of a better way of doing this, because having buffer index ops in-line causes 
        // typechecking errors. So here I declare a whole range of let bindings for the 32 elements of t
	// starting at index j. I'm open to suggestions for a better way of doing this.
	let tj   = t.(j)          in let tj1 = t.(j+.size 1)   in let tj2  = t.(j+.size 2)  in let tj3  = t.(j+.size 3) in
	let tj4  = t.(j+.size 4)  in let tj5 = t.(j+.size 5)   in let tj6  = t.(j+.size 6)  in let tj7  = t.(j+.size 7) in
	let tj8  = t.(j+.size 8)  in let tj9 = t.(j+.size 9)   in let tj10 = t.(j+.size 10) in let tj11 = t.(j+.size 11) in
	let tj12 = t.(j+.size 12) in let tj13 = t.(j+.size 13) in let tj14 = t.(j+.size 14) in let tj15 = t.(j+.size 15) in
	let tj16 = t.(j+.size 16) in let tj17 = t.(j+.size 17) in let tj18 = t.(j+.size 18) in let tj19 = t.(j+.size 19) in
	let tj20 = t.(j+.size 20) in let tj21 = t.(j+.size 21) in let tj22 = t.(j+.size 22) in let tj23 = t.(j+.size 23) in
	let tj24 = t.(j+.size 24) in let tj25 = t.(j+.size 25) in let tj26 = t.(j+.size 26) in let tj27 = t.(j+.size 27) in
	let tj28 = t.(j+.size 28) in let tj29 = t.(j+.size 29) in let tj30 = t.(j+.size 30) in let tj31 = t.(j+.size 31) in

        pt (i)          (tj               |^ (tj1  <<^ 23ul)); 
	pt (i+.size 1)  ((tj1  >>^ 9ul)   |^ (tj2  <<^ 14ul)); pt (i+.size 2)   ((tj2  >>^ 18ul)  |^ (tj3  <<^  5ul) |^ (tj4 <<^ 28ul)); 
	pt (i+.size 3)  ((tj4  >>^  4ul)  |^ (tj5  <<^ 19ul));
	pt (i+.size 4)  ((tj5  >>^ 13ul)  |^ (tj6  <<^ 10ul)); pt (i+.size 5)   ((tj6  >>^ 22ul)  |^ (tj7  <<^  1ul) |^ (tj8 <<^ 24ul));
	pt (i+.size 6)  ((tj8  >>^  8ul)  |^ (tj9  <<^ 15ul)); pt (i+.size 7)   ((tj9  >>^ 17ul)  |^ (tj10 <<^ 6ul) |^ (tj11 <<^ 29ul));
	pt (i+.size 8)  ((tj11 >>^  3ul)  |^ (tj12 <<^ 20ul));
	pt (i+.size 9)  ((tj12 >>^ 12ul)  |^ (tj13 <<^ 11ul)); pt (i+.size 10)  ((tj13 >>^ 21ul)  |^ (tj14 <<^  2ul) |^ (tj15 <<^ 25ul));
	pt (i+.size 11) ((tj15 >>^  7ul)  |^ (tj16 <<^ 16ul)); pt (i+.size 12)  ((tj16 >>^ 16ul)  |^ (tj17 <<^  7ul) |^ (tj18 <<^ 30ul));
	pt (i+.size 13) ((tj18 >>^  2ul)  |^ (tj19 <<^ 21ul));
	pt (i+.size 14) ((tj19 >>^ 11ul)  |^ (tj20 <<^ 12ul)); pt (i+.size 15)  ((tj20 >>^ 20ul)  |^ (tj21 <<^  3ul) |^ (tj22 <<^ 26ul));
	pt (i+.size 16) ((tj22 >>^  6ul)  |^ (tj23 <<^ 17ul)); pt (i+.size 17)  ((tj23 >>^ 15ul)  |^ (tj24 <<^  8ul) |^ (tj25 <<^ 31ul));
	pt (i+.size 18) ((tj25 >>^  1ul)  |^ (tj26 <<^ 22ul)); 
	pt (i+.size 19) ((tj26 >>^ 10ul)  |^ (tj27 <<^ 13ul)); pt (i+.size 20)  ((tj27 >>^ 19ul)  |^ (tj28 <<^  4ul) |^ (tj29 <<^ 27ul)); 
	pt (i+.size 21) ((tj29 >>^  5ul)  |^ (tj30 <<^ 18ul));
	pt (i+.size 22) ((tj30 >>^ 14ul)  |^ (tj31 <<^  9ul));
	
        jBuf.(size 0) <- j +. size 32;
	iBuf.(size 0) <- i +. params_q_log
    );

    update_sub #MUT #_ #_ pk (params_n *. params_q_log /. size 8) crypto_seedbytes seedA;
    
    pop_frame()

private inline_for_extraction noextract
val decode_pk_pt:
    pk : lbuffer uint8 crypto_publickeybytes
  -> j : size_t{j <. crypto_publickeybytes /. (size UI32.n /. size 8)}
  -> Stack UI32.t
    (requires fun h -> live h pk)
    (ensures fun h0 _ h1 -> h0 == h1)

let decode_pk_pt pk j =
    uint_from_bytes_le #U32 #PUB (sub pk (j *. size UI32.n /. size 8) (size UI32.n /. size 8))

val decode_pk:
    pk : lbuffer I32.t (params_n *. params_k)
  -> seedA : lbuffer uint8 crypto_seedbytes
  -> pk_in : lbuffer uint8 crypto_publickeybytes
  -> Stack unit
    (requires fun h -> live h pk /\ live h seedA /\ live h pk_in /\ disjoint pk seedA /\ disjoint pk pk_in /\ disjoint seedA pk_in)
    (ensures fun h0 _ h1 -> modifies2 pk seedA h0 h1)

let decode_pk pk seedA pk_in =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in
    // In the reference implementation, pp is a uint32_t view into pk. We can't do that in F*, so we operate
    // directly on pk, doing a cast from int32 to uint32 in-line. pt is a uint32_t view into pk, and the
    // function pt above takes care of doing that conversion.
    let mask23:UI32.t = UI32.((1ul <<^ params_q_log) -^ 1ul) in

    // In the reference code, "pt = (uint32_t*)pk_in" where pk_in is (unsigned char *). We can't recast buffers to have
    // different element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry decode_pk_pt above with pk_in as its first parameter to provide a function that looks a lot
    // like the array dereference in the reference code, and extracts down to load32_le.
    [@inline_let] let pt = decode_pk_pt pk_in in

    while
    #(fun h -> live h pk /\ live h pk_in /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h pk /\ live h pk_in /\ live h iBuf /\ live h jBuf)
    (fun _ -> (iBuf.(size 0)) <. params_n)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in
        // Doing these statements in the form of "pk.(i+.size #) <- UI32.(expression)" causes typechecking problems.
	// Lifting the calculation into a let of time UI32.t and then passing it to uint32_to_int32 works at the
	// expense of junking up the code.
        [@inline_let] let u2i = uint32_to_int32 in
	// In the reference code, assignment is done to pp, and "pp = (uint32_t*)pk". Here instead we inline the
	// cast of the reuslt from uint32_t to int32_t in each assignment and then assign directly to elements of pk.
        let ppi = UI32.( (pt j) &^ mask23 ) in pk.(i) <- u2i ppi;
	let ppi1 = UI32.( (((pt (j+.size  0)) >>^ 23ul) |^ ((pt (j+.size  1))) <<^  9ul) &^ mask23 ) in pk.(i+.size 1) <- u2i ppi1;
	let ppi2 = UI32.( (((pt (j+.size  1)) >>^ 14ul) |^ ((pt (j+.size  2))) <<^ 18ul) &^ mask23 ) in pk.(i+.size 2) <- u2i ppi2;
	let ppi3 = UI32.(  ((pt (j+.size  2)) >>^  5ul) &^ mask23 ) in pk.(i+.size  3) <- u2i ppi3;
	let ppi4 = UI32.( (((pt (j+.size  2)) >>^ 28ul) |^ ((pt (j+.size  3))) <<^  4ul) &^ mask23 ) in pk.(i+.size  4) <- u2i ppi4;
	let ppi5 = UI32.( (((pt (j+.size  3)) >>^ 19ul) |^ ((pt (j+.size  4))) <<^ 13ul) &^ mask23 ) in pk.(i+.size  5) <- u2i ppi5;
	let ppi6 = UI32.( (((pt (j+.size  4)) >>^ 10ul) |^ ((pt (j+.size  5))) <<^ 22ul) &^ mask23 ) in pk.(i+.size  6) <- u2i ppi6;
	let ppi7 = UI32.(  ((pt (j+.size  5)) >>^  1ul) &^ mask23 ) in pk.(i+.size  7) <- u2i ppi7;
	let ppi8 = UI32.( (((pt (j+.size  5)) >>^ 24ul) |^ ((pt (j+.size  6))) <<^  8ul) &^ mask23 ) in pk.(i+.size  8) <- u2i ppi8;
	let ppi9 = UI32.( (((pt (j+.size  6)) >>^ 15ul) |^ ((pt (j+.size  7))) <<^ 17ul) &^ mask23 ) in pk.(i+.size  9) <- u2i ppi9;
	let ppi10 = UI32.(  ((pt (j+.size  7)) >>^  6ul) &^ mask23 ) in pk.(i+.size 10)  <- u2i ppi10;
	let ppi11 = UI32.( (((pt (j+.size  7)) >>^ 29ul) |^ ((pt (j+.size  8))) <<^  3ul) &^  mask23 ) in pk.(i+.size 11) <- u2i ppi11;
	let ppi12 = UI32.( (((pt (j+.size  8)) >>^ 20ul) |^ ((pt (j+.size  9))) <<^ 12ul) &^ mask23 ) in pk.(i+.size 12) <- u2i ppi12;
	let ppi13 = UI32.( (((pt (j+.size  9)) >>^ 11ul) |^ ((pt (j+.size 10))) <<^ 21ul) &^ mask23 ) in pk.(i+.size 13) <- u2i ppi13;
	let ppi14 = UI32.(  ((pt (j+.size 10)) >>^  2ul) &^ mask23 ) in pk.(i+.size 14) <- u2i ppi14;
	let ppi15 = UI32.( (((pt (j+.size 10)) >>^ 25ul) |^ ((pt (j+.size 11))) <<^  7ul) &^ mask23 ) in pk.(i+.size 15) <- u2i ppi15;
	let ppi16 = UI32.( (((pt (j+.size 11)) >>^ 16ul) |^ ((pt (j+.size 12))) <<^ 16ul) &^ mask23 ) in pk.(i+.size 16) <- u2i ppi16;
	let ppi17 = UI32.(  ((pt (j+.size 12)) >>^  7ul) &^ mask23 ) in pk.(i+.size 17) <- u2i ppi17;
	let ppi18 = UI32.( (((pt (j+.size 12)) >>^ 30ul) |^ ((pt (j+.size 13))) <<^  2ul) &^ mask23 ) in pk.(i+.size 18) <- u2i ppi18;
	let ppi19 = UI32.( (((pt (j+.size 13)) >>^ 21ul) |^ ((pt (j+.size 14))) <<^ 11ul) &^ mask23 ) in pk.(i+.size 19) <- u2i ppi19;
	let ppi20 = UI32.( (((pt (j+.size 14)) >>^ 12ul) |^ ((pt (j+.size 15))) <<^ 20ul) &^ mask23 ) in pk.(i+.size 20) <- u2i ppi20;
	let ppi21 = UI32.(  ((pt (j+.size 15)) >>^  3ul) &^ mask23 ) in pk.(i+.size 21) <- u2i ppi21;
	let ppi22 = UI32.( (((pt (j+.size 15)) >>^ 26ul) |^ ((pt (j+.size 16))) <<^  6ul) &^ mask23 ) in pk.(i+.size 22) <- u2i ppi22;
	let ppi23 = UI32.( (((pt (j+.size 16)) >>^ 17ul) |^ ((pt (j+.size 17))) <<^ 15ul) &^ mask23 ) in pk.(i+.size 23) <- u2i ppi23;
	let ppi24 = UI32.(  ((pt (j+.size 17)) >>^  8ul) &^ mask23 ) in pk.(i+.size 24) <- u2i ppi24;
	let ppi25 = UI32.( (((pt (j+.size 17)) >>^ 31ul) |^ ((pt (j+.size 18))) <<^  1ul) &^ mask23 ) in pk.(i+.size 25) <- u2i ppi25;
	let ppi26 = UI32.( (((pt (j+.size 18)) >>^ 22ul) |^ ((pt (j+.size 19))) <<^ 10ul) &^ mask23 ) in pk.(i+.size 26) <- u2i ppi26;
	let ppi27 = UI32.( (((pt (j+.size 19)) >>^ 13ul) |^ ((pt (j+.size 20))) <<^ 19ul) &^ mask23 ) in pk.(i+.size 27) <- u2i ppi27;
	let ppi28 = UI32.(  ((pt (j+.size 20)) >>^  4ul) &^ mask23 ) in pk.(i+.size 28) <- u2i ppi28;
	let ppi29 = UI32.( (((pt (j+.size 20)) >>^ 27ul) |^ ((pt (j+.size 21))) <<^  5ul) &^ mask23 ) in pk.(i+.size 29) <- u2i ppi29;
	let ppi30 = UI32.( (((pt (j+.size 21)) >>^ 18ul) |^ ((pt (j+.size 22))) <<^ 14ul) &^ mask23 ) in pk.(i+.size 30) <- u2i ppi30;
	let ppi31 = UI32.( (pt (j+.size 22)) >>^  9ul ) in pk.(i+.size 31) <- u2i ppi31;

        jBuf.(size 0) <- j +. size 23;
	iBuf.(size 0) <- i +. size 32
    );

    assert(v params_k = 1);
    copy seedA (sub pk_in (params_n *. params_q_log /. size 8) crypto_seedbytes);

    pop_frame()

// Set an element of an unsigned char array as if it were a uint32
private inline_for_extraction noextract
val encode_sig_ptSet:
    buf : lbuffer uint8 crypto_bytes
  -> i : size_t{i <. crypto_bytes /. (size UI32.n /. size 8)}
  -> value : UI32.t
  -> Stack unit
    (requires fun h -> live h buf)
    (ensures fun h0 _ h1 -> modifies1 buf h0 h1)

let encode_sig_ptSet buf i value = 
    uint_to_bytes_le #U32 #_ (sub buf (i *. size UI32.n /. size 8) (size UI32.n /. size 8)) value

private inline_for_extraction noextract
val encode_sig_tGet:
    z : poly
  -> j : size_t{j <. params_n *. params_k *. (size elem_n /. size 8) /. (size UI64.n /. size 8)}
  -> Stack UI32.t
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

let encode_sig_tGet z j = 
    let zj = z.(j) in elem_to_uint32 zj

val encode_sig:
    sm : lbuffer uint8 crypto_bytes
  -> c : lbuffer uint8 crypto_c_bytes
  -> z : poly
  -> Stack unit
    (requires fun h -> live h sm /\ live h c /\ live h z /\ disjoint sm c /\ disjoint sm z /\ disjoint c z)
    (ensures fun h0 _ h1 -> modifies1 sm h0 h1)

let encode_sig sm c z =
    push_frame();
    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in

    // Can't use t for this definition, because t is defined in UI64 as a type and overrides this definition when we
    // qualify the below expressions in the UI64 module's namespace.
    [@inline_let] let t_ = encode_sig_tGet z in
    [@inline_let] let pt = encode_sig_ptSet sm in

    while
    #(fun h -> live h sm /\ live h c /\ live h z /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h sm /\ live h c /\ live h z /\ live h iBuf /\ live h jBuf)
    (fun _ -> iBuf.(size 0) <. params_n *. params_d /. size 32)
    (fun _ ->
        let i:size_t = iBuf.(size 0) in
	let j:size_t = jBuf.(size 0) in

        pt i            UI32.( ((t_ j)                        &^ ((1ul <<^ 21ul) -^ 1ul)) |^ ((t_ (j+.size  1)) <<^ 21ul) );
	pt (i+.size  1) UI32.( (((t_ (j +.size  1)) >>^ 11ul) &^ ((1ul <<^ 10ul) -^ 1ul)) |^ (((t_ (j+.size  2)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^ 10ul) |^ ((t_ (j+.size  3)) <<^ 31ul) );
	pt (i+.size  2) UI32.( (((t_ (j +.size  3)) >>^  1ul) &^ ((1ul <<^ 20ul) -^ 1ul)) |^ ((t_ (j+.size  4)) <<^ 20ul) );
	pt (i+.size  3) UI32.( (((t_ (j +.size  4)) >>^ 12ul) &^ ((1ul <<^  9ul) -^ 1ul)) |^ (((t_ (j+.size  5)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  9ul) |^ ((t_ (j+.size  6)) <<^ 30ul) );
	pt (i+.size  4) UI32.( (((t_ (j +.size  6)) >>^  2ul) &^ ((1ul <<^ 19ul) -^ 1ul)) |^ ((t_ (j+.size  7)) <<^ 19ul) );
	pt (i+.size  5) UI32.( (((t_ (j +.size  7)) >>^ 13ul) &^ ((1ul <<^  8ul) -^ 1ul)) |^ (((t_ (j+.size  8)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  8ul) |^ ((t_ (j+.size  9)) <<^ 29ul) );
	pt (i+.size  6) UI32.( (((t_ (j +.size  9)) >>^  3ul) &^ ((1ul <<^ 18ul) -^ 1ul)) |^ ((t_ (j+.size 10)) <<^ 18ul) );
	pt (i+.size  7) UI32.( (((t_ (j +.size 10)) >>^ 14ul) &^ ((1ul <<^  7ul) -^ 1ul)) |^ (((t_ (j+.size 11)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  7ul) |^ ((t_ (j+.size 12)) <<^ 28ul) );
	pt (i+.size  8) UI32.( (((t_ (j +.size 12)) >>^  4ul) &^ ((1ul <<^ 17ul) -^ 1ul)) |^ ((t_ (j+.size 13)) <<^ 17ul) );
	pt (i+.size  9) UI32.( (((t_ (j +.size 13)) >>^ 15ul) &^ ((1ul <<^  6ul) -^ 1ul)) |^ (((t_ (j+.size 14)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  6ul) |^ ((t_ (j+.size 15)) <<^ 27ul) );
	pt (i+.size 10) UI32.( (((t_ (j +.size 15)) >>^  5ul) &^ ((1ul <<^ 16ul) -^ 1ul)) |^ ((t_ (j+.size 16)) <<^ 16ul) );
	pt (i+.size 11) UI32.( (((t_ (j +.size 16)) >>^ 16ul) &^ ((1ul <<^  5ul) -^ 1ul)) |^ (((t_ (j+.size 17)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  5ul) |^ ((t_ (j+.size 18)) <<^ 26ul) );
	pt (i+.size 12) UI32.( (((t_ (j +.size 18)) >>^  6ul) &^ ((1ul <<^ 15ul) -^ 1ul)) |^ ((t_ (j+.size 19)) <<^ 15ul) );
	pt (i+.size 13) UI32.( (((t_ (j +.size 19)) >>^ 17ul) &^ ((1ul <<^  4ul) -^ 1ul)) |^ (((t_ (j+.size 20)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  4ul) |^ ((t_ (j+.size 21)) <<^ 25ul) );
	pt (i+.size 14) UI32.( (((t_ (j +.size 21)) >>^  7ul) &^ ((1ul <<^ 14ul) -^ 1ul)) |^ ((t_ (j+.size 22)) <<^ 14ul) );
	pt (i+.size 15) UI32.( (((t_ (j +.size 22)) >>^ 18ul) &^ ((1ul <<^  3ul) -^ 1ul)) |^ (((t_ (j+.size 23)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  3ul) |^ ((t_ (j+.size 24)) <<^ 24ul) );
	pt (i+.size 16) UI32.( (((t_ (j +.size 24)) >>^  8ul) &^ ((1ul <<^ 13ul) -^ 1ul)) |^ ((t_ (j+.size 25)) <<^ 13ul) );
	pt (i+.size 17) UI32.( (((t_ (j +.size 25)) >>^ 19ul) &^ ((1ul <<^  2ul) -^ 1ul)) |^ (((t_ (j+.size 26)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  2ul) |^ ((t_ (j+.size 27)) <<^ 23ul) );
	pt (i+.size 18) UI32.( (((t_ (j +.size 27)) >>^  9ul) &^ ((1ul <<^ 12ul) -^ 1ul)) |^ ((t_ (j+.size 28)) <<^ 12ul) );
	pt (i+.size 19) UI32.( (((t_ (j +.size 28)) >>^ 20ul) &^ ((1ul <<^  1ul) -^ 1ul)) |^ (((t_ (j+.size 29)) &^ ((1ul <<^ 21ul) -^ 1ul)) <<^  1ul) |^ ((t_ (j+.size 30)) <<^ 22ul) );
	pt (i+.size 20) UI32.( (((t_ (j +.size 30)) >>^ 10ul) &^ ((1ul <<^ 11ul) -^ 1ul)) |^ ((t_ (j+.size 31)) <<^ 11ul) );

        jBuf.(size 0) <- j +. size 32;
	iBuf.(size 0) <- i +. params_d
    );

    update_sub #MUT #_ #_ sm (params_n *. params_d /. size 8) crypto_c_bytes c;

    pop_frame()

private inline_for_extraction noextract
val decode_sig_pt:
    smlen : size_t
  -> sm : lbuffer uint8 smlen
  -> j : size_t{j <. smlen /. (size UI32.n /. size 8)}
  -> Stack UI32.t
    (requires fun h -> live h sm)
    (ensures fun h0 _ h1 -> h0 == h1)

let decode_sig_pt smlen sm j =
    uint_from_bytes_le #U32 #PUB (sub sm (j *. size UI32.n /. size 8) (size UI32.n /. size 8))

val decode_sig:
    c: lbuffer uint8 crypto_c_bytes
  -> z: poly
  -> smlen : size_t
  -> sm: lbuffer uint8 smlen
  -> Stack unit
    (requires fun h -> live h c /\ live h z /\ live h sm /\ disjoint c z /\ disjoint c sm /\ disjoint z sm)
    (ensures fun h0 _ h1 -> modifies2 c z h0 h1)

let decode_sig c z smlen sm =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in

    // In the reference code, "pt = (uint32_t*)sm" where sm is (unsigned char *). We can't recast buffers to have
    // different element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry decode_sig_pt above with smlen and sm as its two parameters to provide a function that looks a lot
    // like the array dereference in the reference code, and extracts down to load32_le.
    [@inline_let] let pt = decode_sig_pt smlen sm in

    while
    #(fun h -> live h z /\ live h sm /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h z /\ live h sm /\ live h iBuf /\ live h jBuf)
    (fun _ -> iBuf.(size 0) <. params_n)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in
        [@inline_let] let u2i = uint32_to_int32 in
	[@inline_let] let i2e = int32_to_elem in

        // As above, putting a call to (pt j) inline in these computation causes a typechecking error. Instead we
	// let-bind all the elements of pt we will be working with and use those values in-line.
	let ptj0  = pt (j+.size  0) in	let ptj1  = pt (j+.size  1) in
	let ptj2  = pt (j+.size  2) in	let ptj3  = pt (j+.size  3) in
	let ptj4  = pt (j+.size  4) in	let ptj5  = pt (j+.size  5) in
	let ptj6  = pt (j+.size  6) in	let ptj7  = pt (j+.size  7) in
	let ptj8  = pt (j+.size  8) in	let ptj9  = pt (j+.size  9) in
	let ptj10 = pt (j+.size 10) in  let ptj11 = pt (j+.size 11) in
	let ptj12 = pt (j+.size 12) in  let ptj13 = pt (j+.size 13) in
	let ptj14 = pt (j+.size 14) in  let ptj15 = pt (j+.size 15) in
	let ptj16 = pt (j+.size 16) in  let ptj17 = pt (j+.size 17) in
	let ptj18 = pt (j+.size 18) in  let ptj19 = pt (j+.size 19) in
	let ptj20 = pt (j+.size 20) in
	
	
        z.(i)          <- i2e I32.( u2i UI32.( ptj0 <<^ 11ul ) >>^ 11ul );
        z.(i+.size  1) <- i2e I32.( u2i UI32.( ptj0 >>^ 21ul ) |^ (u2i UI32.(ptj1 <<^ 22ul)) >>^ 11ul );
        z.(i+.size  2) <- i2e I32.( u2i UI32.( ptj1 <<^  1ul ) >>^ 11ul );
        z.(i+.size  3) <- i2e I32.( u2i UI32.( ptj1 >>^ 31ul ) |^ (u2i UI32.(ptj2 <<^ 12ul)) >>^ 11ul );
        z.(i+.size  4) <- i2e I32.( u2i UI32.( ptj2 >>^ 20ul ) |^ (u2i UI32.(ptj3 <<^ 23ul)) >>^ 11ul );
        z.(i+.size  5) <- i2e I32.( u2i UI32.( ptj3 <<^  2ul ) >>^ 11ul );
        z.(i+.size  6) <- i2e I32.( u2i UI32.( ptj3 >>^ 30ul ) |^ (u2i UI32.(ptj4 <<^ 13ul)) >>^ 11ul );
        z.(i+.size  7) <- i2e I32.( u2i UI32.( ptj4 >>^ 19ul ) |^ (u2i UI32.(ptj5 <<^ 24ul)) >>^ 11ul );
        z.(i+.size  8) <- i2e I32.( u2i UI32.( ptj5 <<^  3ul ) >>^ 11ul );
        z.(i+.size  9) <- i2e I32.( u2i UI32.( ptj5 >>^ 29ul ) |^ (u2i UI32.(ptj6 <<^ 14ul)) >>^ 11ul );
        z.(i+.size 10) <- i2e I32.( u2i UI32.( ptj6 >>^ 18ul ) |^ (u2i UI32.(ptj7 <<^ 25ul)) >>^ 11ul );
        z.(i+.size 11) <- i2e I32.( u2i UI32.( ptj7 <<^  4ul ) >>^ 11ul );
        z.(i+.size 12) <- i2e I32.( u2i UI32.( ptj7 >>^ 28ul ) |^ (u2i UI32.(ptj8 <<^ 15ul)) >>^ 11ul );
        z.(i+.size 13) <- i2e I32.( u2i UI32.( ptj8 >>^ 17ul ) |^ (u2i UI32.(ptj9 <<^ 26ul)) >>^ 11ul );
        z.(i+.size 14) <- i2e I32.( u2i UI32.( ptj9 <<^  5ul ) >>^ 11ul );
        z.(i+.size 15) <- i2e I32.( u2i UI32.( ptj9 >>^ 27ul ) |^ (u2i UI32.(ptj10 <<^ 16ul)) >>^ 11ul );
        z.(i+.size 16) <- i2e I32.( u2i UI32.( ptj10 >>^ 16ul ) |^ (u2i UI32.(ptj11 <<^ 27ul)) >>^ 11ul );
        z.(i+.size 17) <- i2e I32.( u2i UI32.( ptj11 <<^  6ul ) >>^ 11ul );
        z.(i+.size 18) <- i2e I32.( u2i UI32.( ptj11 >>^ 26ul ) |^ (u2i UI32.(ptj12 <<^ 17ul)) >>^ 11ul );
        z.(i+.size 19) <- i2e I32.( u2i UI32.( ptj12 >>^ 15ul ) |^ (u2i UI32.(ptj13 <<^ 28ul)) >>^ 11ul );
        z.(i+.size 20) <- i2e I32.( u2i UI32.( ptj13 <<^  7ul ) >>^ 11ul );
        z.(i+.size 21) <- i2e I32.( u2i UI32.( ptj13 >>^ 25ul ) |^ (u2i UI32.(ptj14 <<^ 18ul)) >>^ 11ul );
        z.(i+.size 22) <- i2e I32.( u2i UI32.( ptj14 >>^ 14ul ) |^ (u2i UI32.(ptj15 <<^ 29ul)) >>^ 11ul );
        z.(i+.size 23) <- i2e I32.( u2i UI32.( ptj15 <<^  8ul ) >>^ 11ul );
        z.(i+.size 24) <- i2e I32.( u2i UI32.( ptj15 >>^ 24ul ) |^ (u2i UI32.(ptj16 <<^ 19ul)) >>^ 11ul );
        z.(i+.size 25) <- i2e I32.( u2i UI32.( ptj16 >>^ 13ul ) |^ (u2i UI32.(ptj17 <<^ 30ul)) >>^ 11ul );
        z.(i+.size 26) <- i2e I32.( u2i UI32.( ptj17 <<^  9ul ) >>^ 11ul );
        z.(i+.size 27) <- i2e I32.( u2i UI32.( ptj17 >>^ 23ul ) |^ (u2i UI32.(ptj18 <<^ 20ul)) >>^ 11ul );
        z.(i+.size 28) <- i2e I32.( u2i UI32.( ptj18 >>^ 12ul ) |^ (u2i UI32.(ptj19 <<^ 31ul)) >>^ 11ul );
        z.(i+.size 29) <- i2e I32.( u2i UI32.( ptj19 <<^ 10ul ) >>^ 11ul );
        z.(i+.size 30) <- i2e I32.( u2i UI32.( ptj19 >>^ 22ul ) |^ (u2i UI32.(ptj20 <<^ 21ul)) >>^ 11ul );
	z.(i+.size 31) <- i2e I32.( u2i ptj20 >>^ 11ul );

        jBuf.(size 0) <- j +. size 21;
	iBuf.(size 0) <- i +. size 32
    );

    copy c (sub sm (params_n *. params_d /. size 8) crypto_c_bytes);

    pop_frame()
