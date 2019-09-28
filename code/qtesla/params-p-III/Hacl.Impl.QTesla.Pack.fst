module Hacl.Impl.QTesla.Pack

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

module SHA3 = Hacl.SHA3
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
open Hacl.Impl.QTesla.Globals

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

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

    while
    #(fun h -> live h t /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h t /\ live h iBuf /\ live h jBuf)
    (fun _ -> (iBuf.(size 0)) <. params_n *. params_k *. params_q_log /. size 32)
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

        pt (i)          (tj               |^ (tj1  <<^ 31ul));
	pt (i+.size 1)  ((tj1  >>^  1ul)  |^ (tj2  <<^ 30ul)); pt (i+.size 2)   ((tj2  >>^  2ul)  |^ (tj3  <<^ 29ul));
	pt (i+.size 3)  ((tj3  >>^  3ul)  |^ (tj4  <<^ 28ul)); pt (i+.size 4)   ((tj4  >>^  4ul)  |^ (tj5  <<^ 27ul));
	pt (i+.size 5)  ((tj5  >>^  5ul)  |^ (tj6  <<^ 26ul)); pt (i+.size 6)   ((tj6  >>^  6ul)  |^ (tj7  <<^ 25ul));
	pt (i+.size 7)  ((tj7  >>^  7ul)  |^ (tj8  <<^ 24ul)); pt (i+.size 8)   ((tj8  >>^  8ul)  |^ (tj9  <<^ 23ul));
	pt (i+.size 9)  ((tj9  >>^  9ul)  |^ (tj10 <<^ 22ul)); pt (i+.size 10)  ((tj10 >>^ 10ul)  |^ (tj11 <<^ 21ul));
	pt (i+.size 11) ((tj11 >>^ 11ul)  |^ (tj12 <<^ 20ul)); pt (i+.size 12)  ((tj12 >>^ 12ul)  |^ (tj13 <<^ 19ul));
	pt (i+.size 13) ((tj13 >>^ 13ul)  |^ (tj14 <<^ 18ul)); pt (i+.size 14)  ((tj14 >>^ 14ul)  |^ (tj15 <<^ 17ul));
	pt (i+.size 15) ((tj15 >>^ 15ul)  |^ (tj16 <<^ 16ul)); pt (i+.size 16)  ((tj16 >>^ 16ul)  |^ (tj17 <<^ 15ul));
	pt (i+.size 17) ((tj17 >>^ 17ul)  |^ (tj18 <<^ 14ul)); pt (i+.size 18)  ((tj18 >>^ 18ul)  |^ (tj19 <<^ 13ul));
	pt (i+.size 19) ((tj19 >>^ 19ul)  |^ (tj20 <<^ 12ul)); pt (i+.size 20)  ((tj20 >>^ 20ul)  |^ (tj21 <<^ 11ul));
	pt (i+.size 21) ((tj21 >>^ 21ul)  |^ (tj22 <<^ 10ul)); pt (i+.size 22)  ((tj22 >>^ 22ul)  |^ (tj23 <<^  9ul));
	pt (i+.size 23) ((tj23 >>^ 23ul)  |^ (tj24 <<^  8ul)); pt (i+.size 24)  ((tj24 >>^ 24ul)  |^ (tj25 <<^  7ul));
	pt (i+.size 25) ((tj25 >>^ 25ul)  |^ (tj26 <<^  6ul)); pt (i+.size 26)  ((tj26 >>^ 26ul)  |^ (tj27 <<^  5ul));
	pt (i+.size 27) ((tj27 >>^ 27ul)  |^ (tj28 <<^  4ul)); pt (i+.size 28)  ((tj28 >>^ 28ul)  |^ (tj29 <<^  3ul));
	pt (i+.size 29) ((tj29 >>^ 29ul)  |^ (tj30 <<^  2ul)); pt (i+.size 30)  ((tj30 >>^ 30ul)  |^ (tj31 <<^  1ul));
	
        jBuf.(size 0) <- j +. size 32;
	iBuf.(size 0) <- i +. params_q_log
    );

    update_sub #MUT #_ #_ pk (params_n *. params_k *. params_q_log /. size 8) crypto_seedbytes seedA;
    
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
    let mask31:UI32.t = UI32.((1ul <<^ params_q_log) -^ 1ul) in

    // In the reference code, "pt = (uint32_t*)pk_in" where pk_in is (unsigned char *). We can't recast buffers to have
    // different element types in F*. (BufferView does this, but only as ghost predicates for proving theorems.)
    // Instead, we curry decode_pk_pt above with pk_in as its first parameter to provide a function that looks a lot
    // like the array dereference in the reference code, and extracts down to load32_le.
    [@inline_let] let pt = decode_pk_pt pk_in in

    while
    #(fun h -> live h pk /\ live h pk_in /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h pk /\ live h pk_in /\ live h iBuf /\ live h jBuf)
    (fun _ -> (iBuf.(size 0)) <. (params_n *. params_k))
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in
        // Doing these statements in the form of "pk.(i+.size #) <- UI32.(expression)" causes typechecking problems.
	// Lifting the calculation into a let of time UI32.t and then passing it to uint32_to_int32 works at the
	// expense of junking up the code.
        [@inline_let] let u2i = uint32_to_int32 in
	// In the reference code, assignment is done to pp, and "pp = (uint32_t*)pk". Here instead we inline the
	// cast of the reuslt from uint32_t to int32_t in each assignment and then assign directly to elements of pk.
        let ppi = UI32.( (pt j) &^ mask31 ) in pk.(i) <- u2i ppi;
	let ppi1 = UI32.( (((pt (j+.size  0)) >>^ 31ul) |^ ((pt (j+.size  1))) <<^  1ul) &^ mask31 ) in pk.(i+.size 1) <- u2i ppi1;
	let ppi2 = UI32.( (((pt (j+.size  1)) >>^ 30ul) |^ ((pt (j+.size  2))) <<^  2ul) &^ mask31 ) in pk.(i+.size 2) <- u2i ppi2;
	let ppi3 = UI32.( (((pt (j+.size  2)) >>^ 29ul) |^ ((pt (j+.size  3))) <<^  3ul) &^ mask31 ) in pk.(i+.size  3) <- u2i ppi3;
	let ppi4 = UI32.( (((pt (j+.size  3)) >>^ 28ul) |^ ((pt (j+.size  4))) <<^  4ul) &^ mask31 ) in pk.(i+.size  4) <- u2i ppi4;
	let ppi5 = UI32.( (((pt (j+.size  4)) >>^ 27ul) |^ ((pt (j+.size  5))) <<^  5ul) &^ mask31 ) in pk.(i+.size  5) <- u2i ppi5;
	let ppi6 = UI32.( (((pt (j+.size  5)) >>^ 26ul) |^ ((pt (j+.size  6))) <<^  6ul) &^ mask31 ) in pk.(i+.size  6) <- u2i ppi6;
	let ppi7 = UI32.( (((pt (j+.size  6)) >>^ 25ul) |^ ((pt (j+.size  7))) <<^  7ul) &^ mask31 ) in pk.(i+.size  7) <- u2i ppi7;
	let ppi8 = UI32.( (((pt (j+.size  7)) >>^ 24ul) |^ ((pt (j+.size  8))) <<^  8ul) &^ mask31 ) in pk.(i+.size  8) <- u2i ppi8;
	let ppi9 = UI32.( (((pt (j+.size  8)) >>^ 23ul) |^ ((pt (j+.size  9))) <<^  9ul) &^ mask31 ) in pk.(i+.size  9) <- u2i ppi9;
	let ppi10 = UI32.( (((pt (j+.size  9)) >>^ 22ul) |^ ((pt (j+.size 10))) <<^ 10ul) &^ mask31 ) in pk.(i+.size 10)  <- u2i ppi10;
	let ppi11 = UI32.( (((pt (j+.size 10)) >>^ 21ul) |^ ((pt (j+.size 11))) <<^ 11ul) &^  mask31 ) in pk.(i+.size 11) <- u2i ppi11;
	let ppi12 = UI32.( (((pt (j+.size 11)) >>^ 20ul) |^ ((pt (j+.size 12))) <<^ 12ul) &^ mask31 ) in pk.(i+.size 12) <- u2i ppi12;
	let ppi13 = UI32.( (((pt (j+.size 12)) >>^ 19ul) |^ ((pt (j+.size 13))) <<^ 13ul) &^ mask31 ) in pk.(i+.size 13) <- u2i ppi13;
	let ppi14 = UI32.( (((pt (j+.size 13)) >>^ 18ul) |^ ((pt (j+.size 14))) <<^ 14ul) &^ mask31 ) in pk.(i+.size 14) <- u2i ppi14;
	let ppi15 = UI32.( (((pt (j+.size 14)) >>^ 17ul) |^ ((pt (j+.size 15))) <<^ 15ul) &^ mask31 ) in pk.(i+.size 15) <- u2i ppi15;
	let ppi16 = UI32.( (((pt (j+.size 15)) >>^ 16ul) |^ ((pt (j+.size 16))) <<^ 16ul) &^ mask31 ) in pk.(i+.size 16) <- u2i ppi16;
	let ppi17 = UI32.( (((pt (j+.size 16)) >>^ 15ul) |^ ((pt (j+.size 17))) <<^ 17ul) &^ mask31 ) in pk.(i+.size 17) <- u2i ppi17;
	let ppi18 = UI32.( (((pt (j+.size 17)) >>^ 14ul) |^ ((pt (j+.size 18))) <<^ 18ul) &^ mask31 ) in pk.(i+.size 18) <- u2i ppi18;
	let ppi19 = UI32.( (((pt (j+.size 18)) >>^ 13ul) |^ ((pt (j+.size 19))) <<^ 19ul) &^ mask31 ) in pk.(i+.size 19) <- u2i ppi19;
	let ppi20 = UI32.( (((pt (j+.size 19)) >>^ 12ul) |^ ((pt (j+.size 20))) <<^ 20ul) &^ mask31 ) in pk.(i+.size 20) <- u2i ppi20;
	let ppi21 = UI32.( (((pt (j+.size 20)) >>^ 11ul) |^ ((pt (j+.size 21))) <<^ 21ul) &^ mask31 ) in pk.(i+.size 21) <- u2i ppi21;
	let ppi22 = UI32.( (((pt (j+.size 21)) >>^ 10ul) |^ ((pt (j+.size 22))) <<^ 22ul) &^ mask31 ) in pk.(i+.size 22) <- u2i ppi22;
	let ppi23 = UI32.( (((pt (j+.size 22)) >>^  9ul) |^ ((pt (j+.size 23))) <<^ 23ul) &^ mask31 ) in pk.(i+.size 23) <- u2i ppi23;
	let ppi24 = UI32.( (((pt (j+.size 23)) >>^  8ul) |^ ((pt (j+.size 24))) <<^ 24ul) &^ mask31 ) in pk.(i+.size 24) <- u2i ppi24;
	let ppi25 = UI32.( (((pt (j+.size 24)) >>^  7ul) |^ ((pt (j+.size 25))) <<^ 25ul) &^ mask31 ) in pk.(i+.size 25) <- u2i ppi25;
	let ppi26 = UI32.( (((pt (j+.size 25)) >>^  6ul) |^ ((pt (j+.size 26))) <<^ 26ul) &^ mask31 ) in pk.(i+.size 26) <- u2i ppi26;
	let ppi27 = UI32.( (((pt (j+.size 26)) >>^  5ul) |^ ((pt (j+.size 27))) <<^ 27ul) &^ mask31 ) in pk.(i+.size 27) <- u2i ppi27;
	let ppi28 = UI32.( (((pt (j+.size 27)) >>^  4ul) |^ ((pt (j+.size 28))) <<^ 28ul) &^ mask31 ) in pk.(i+.size 28) <- u2i ppi28;
	let ppi29 = UI32.( (((pt (j+.size 28)) >>^  3ul) |^ ((pt (j+.size 29))) <<^ 29ul) &^ mask31 ) in pk.(i+.size 29) <- u2i ppi29;
	let ppi30 = UI32.( (((pt (j+.size 29)) >>^  2ul) |^ ((pt (j+.size 30))) <<^ 30ul) &^ mask31 ) in pk.(i+.size 30) <- u2i ppi30;
	let ppi31 = UI32.( (pt (j+.size 30)) >>^  1ul ) in pk.(i+.size 31) <- u2i ppi31;

        jBuf.(size 0) <- j +. size 31;
	iBuf.(size 0) <- i +. size 32
    );

    copy seedA (sub pk_in (params_n *. params_k *. params_q_log /. size 8) crypto_seedbytes);

    pop_frame()

// Set an element of an unsigned char array as if it were a uint32
private inline_for_extraction noextract
val encode_sig_ptSet:
    buf : lbuffer uint8 crypto_bytes
  -> i : size_t{i <. crypto_bytes /. (size UI32.n /. size 8)}
  -> value : UI64.t
  -> Stack unit
    (requires fun h -> live h buf)
    (ensures fun h0 _ h1 -> modifies1 buf h0 h1)

let encode_sig_ptSet buf i value = 
    uint_to_bytes_le #U32 #_ (sub buf (i *. size UI32.n /. size 8) (size UI32.n /. size 8)) (uint64_to_uint32 value)

private inline_for_extraction noextract
val encode_sig_tGet:
    z : poly
  -> j : size_t{j <. params_n *. params_k *. (size elem_n /. size 8) /. (size UI64.n /. size 8)}
  -> Stack UI64.t
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

let encode_sig_tGet z j = 
    let zj = z.(j) in elem_to_uint64 zj

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

        pt i            UI64.( ((t_ j)                        &^ ((1uL <<^ 24ul) -^ 1uL)) |^ ((t_ (j+.size  1)) <<^ 24ul) );
	pt (i+.size  1) UI64.( (((t_ (j +.size  1)) >>^  8ul) &^ ((1uL <<^ 16ul) -^ 1uL)) |^ ((t_ (j+.size  2)) <<^ 16ul) );
	pt (i+.size  2) UI64.( (((t_ (j +.size  2)) >>^ 16ul) &^ ((1uL <<^  8ul) -^ 1uL)) |^ ((t_ (j+.size  3)) <<^  8ul) );

        jBuf.(size 0) <- j +. size 4;
	iBuf.(size 0) <- i +. params_d /. size 8
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
	let ptj0  = pt (j+.size  0) in
	let ptj1  = pt (j+.size  1) in
	let ptj2  = pt (j+.size  2) in

        z.(i)          <- i2e I32.( ((u2i ptj0) <<^  8ul) >>^  8ul );
        z.(i+.size  1) <- i2e I32.( u2i UI32.( (ptj0 >>^ 24ul) &^ ((1ul <<^  8ul) -^ 1ul) ) |^ ((u2i UI32.(ptj1 <<^ 16ul)) >>^  8ul ));
        z.(i+.size  2) <- i2e I32.( u2i UI32.( (ptj1 >>^ 16ul) &^ ((1ul <<^ 16ul) -^ 1ul) ) |^ ((u2i UI32.(ptj2 <<^ 24ul)) >>^  8ul ));
        z.(i+.size  3) <- i2e I32.( (u2i ptj2) >>^ 8ul );

        jBuf.(size 0) <- j +. size 3;
	iBuf.(size 0) <- i +. size 4
    );

    copy c (sub sm (params_n *. params_d /. size 8) crypto_c_bytes);

    pop_frame()

inline_for_extraction noextract
let pack_sk = Hacl.Impl.QTesla.Provable.Pack.pack_sk

inline_for_extraction noextract
let decode_sk = Hacl.Impl.QTesla.Provable.Pack.decode_sk

inline_for_extraction noextract
let encode_or_pack_sk = Hacl.Impl.QTesla.Provable.Pack.encode_or_pack_sk
