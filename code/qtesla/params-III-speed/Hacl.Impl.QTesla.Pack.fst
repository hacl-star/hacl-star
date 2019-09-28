module Hacl.Impl.QTesla.Pack

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

module SHA3 = Hacl.SHA3
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module UI8 = FStar.UInt8
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

val encode_sk:
    sk: lbuffer uint8 crypto_secretkeybytes
  -> s: poly
  -> e: poly_k
  -> seeds: lbuffer uint8 (size 2 *. crypto_seedbytes)
  -> Stack unit
    (requires fun h -> live h sk /\ live h s /\ live h e /\ live h seeds /\
                    disjoint sk s /\ disjoint sk e /\ disjoint sk seeds /\
                    disjoint s e /\ disjoint s seeds /\ disjoint e seeds)
    (ensures fun h0 _ h1 -> modifies1 sk h0 h1)

let encode_sk sk s e seeds =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in

    while
    #(fun h -> live h iBuf /\ live h jBuf /\ live h sk /\ live h s)
    #(fun _ h -> live h iBuf /\ live h jBuf /\ live h sk /\ live h s)
    (fun _ -> iBuf.(size 0) <. params_n)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in
	
        let si0 = s.(i+.size 0) in    let si1 = s.(i+.size 1) in
	let si2 = s.(i+.size 2) in    let si3 = s.(i+.size 3) in
	let si4 = s.(i+.size 4) in    let si5 = s.(i+.size 5) in
	let si6 = s.(i+.size 6) in    let si7 = s.(i+.size 7) in
	
	sk.(j+.size 0) <- elem_to_uint8 si0;
	sk.(j+.size 1) <- elem_to_uint8 (((si0 >>^ 8ul) &^ 0x01l) |^ (si1 <<^ 1ul));
	sk.(j+.size 2) <- elem_to_uint8 (((si1 >>^ 7ul) &^ 0x03l) |^ (si2 <<^ 2ul));
	sk.(j+.size 3) <- elem_to_uint8 (((si2 >>^ 6ul) &^ 0x07l) |^ (si3 <<^ 3ul));
	sk.(j+.size 4) <- elem_to_uint8 (((si3 >>^ 5ul) &^ 0x0fl) |^ (si4 <<^ 4ul));
	sk.(j+.size 5) <- elem_to_uint8 (((si4 >>^ 4ul) &^ 0x1fl) |^ (si5 <<^ 5ul));
	sk.(j+.size 6) <- elem_to_uint8 (((si5 >>^ 3ul) &^ 0x3fl) |^ (si6 <<^ 6ul));
	sk.(j+.size 7) <- elem_to_uint8 (((si6 >>^ 2ul) &^ 0x7fl) |^ (si7 <<^ 7ul));
	sk.(j+.size 8) <- elem_to_uint8 (si7 >>^ 1ul);

        jBuf.(size 0) <- j +. size 9;
	iBuf.(size 0) <- i +. size 8
    );

    iBuf.(size 0) <- size 0;
    
    while
    #(fun h -> live h iBuf /\ live h jBuf /\ live h sk /\ live h e)
    #(fun _ h -> live h iBuf /\ live h jBuf /\ live h sk /\ live h e)
    (fun _ -> iBuf.(size 0) <. params_n)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in

        let ei0 = e.(i+.size 0) in    let ei1 = e.(i+.size 1) in
	let ei2 = e.(i+.size 2) in    let ei3 = e.(i+.size 3) in
	let ei4 = e.(i+.size 4) in    let ei5 = e.(i+.size 5) in
	let ei6 = e.(i+.size 6) in    let ei7 = e.(i+.size 7) in
	
	sk.(j+.size 0) <- elem_to_uint8 ei0;
	sk.(j+.size 1) <- elem_to_uint8 (((ei0 >>^ 8ul) &^ 0x01l) |^ (ei1 <<^ 1ul));
	sk.(j+.size 2) <- elem_to_uint8 (((ei1 >>^ 7ul) &^ 0x03l) |^ (ei2 <<^ 2ul));
	sk.(j+.size 3) <- elem_to_uint8 (((ei2 >>^ 6ul) &^ 0x07l) |^ (ei3 <<^ 3ul));
	sk.(j+.size 4) <- elem_to_uint8 (((ei3 >>^ 5ul) &^ 0x0fl) |^ (ei4 <<^ 4ul));
	sk.(j+.size 5) <- elem_to_uint8 (((ei4 >>^ 4ul) &^ 0x1fl) |^ (ei5 <<^ 5ul));
	sk.(j+.size 6) <- elem_to_uint8 (((ei5 >>^ 3ul) &^ 0x3fl) |^ (ei6 <<^ 6ul));
	sk.(j+.size 7) <- elem_to_uint8 (((ei6 >>^ 2ul) &^ 0x7fl) |^ (ei7 <<^ 7ul));
	sk.(j+.size 8) <- elem_to_uint8 (ei7 >>^ 1ul);

        jBuf.(size 0) <- j +. size 9;
	iBuf.(size 0) <- i +. size 8
    );

    update_sub #MUT #_ #_ sk (size 2 *. params_s_bits *. params_n /. size 8) (size 2 *. crypto_seedbytes) seeds;

    pop_frame()
	
inline_for_extraction noextract
let encode_or_pack_sk = encode_sk

val decode_sk:
    seeds : lbuffer uint8 (size 2 *. crypto_seedbytes)
  -> s : lbuffer I16.t params_n
  -> e : lbuffer I16.t params_n
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack unit
    (requires fun h -> live h seeds /\ live h s /\ live h e /\ live h sk /\
                    disjoint seeds s /\ disjoint seeds e /\ disjoint seeds e /\
		    disjoint s e /\ disjoint s sk /\ disjoint e sk)
    // TODO: fix ensures clause		    
    (ensures fun h0 _ h1 -> True) // modifies (loc_union (loc_union (loc_buffer seeds) (loc_buffer s)) (loc_buffer e)) h0 h1)

let decode_sk seeds s e sk =
    push_frame();

    let iBuf = create (size 1) (size 0) in
    let jBuf = create (size 1) (size 0) in

    while
    #(fun h -> live h s /\ live h sk /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h s /\ live h sk /\ live h iBuf /\ live h jBuf)
    (fun _ -> iBuf.(size 0) <. params_n)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in

        let skj0 = sk.(j+.size 0) in    let skj1 = sk.(j+.size 1) in
	let skj2 = sk.(j+.size 2) in    let skj3 = sk.(j+.size 3) in
	let skj4 = sk.(j+.size 4) in    let skj5 = sk.(j+.size 5) in
	let skj6 = sk.(j+.size 6) in    let skj7 = sk.(j+.size 7) in
	let skj8 = sk.(j+.size 8) in

        s.(i+.size 0) <- I16.(uint8_to_int16 skj0               |^ int32_to_int16 I32.(((uint8_to_int32 skj1) <<^ 31ul) >>^ 23ul));
	s.(i+.size 1) <- I16.(uint8_to_int16 UI8.(skj1 >>^ 1ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj2) <<^ 30ul) >>^ 23ul));
	s.(i+.size 2) <- I16.(uint8_to_int16 UI8.(skj2 >>^ 2ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj3) <<^ 29ul) >>^ 23ul));
	s.(i+.size 3) <- I16.(uint8_to_int16 UI8.(skj3 >>^ 3ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj4) <<^ 28ul) >>^ 23ul));
	s.(i+.size 4) <- I16.(uint8_to_int16 UI8.(skj4 >>^ 4ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj5) <<^ 27ul) >>^ 23ul));
	s.(i+.size 5) <- I16.(uint8_to_int16 UI8.(skj5 >>^ 5ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj6) <<^ 26ul) >>^ 23ul));
	s.(i+.size 6) <- I16.(uint8_to_int16 UI8.(skj6 >>^ 6ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj7) <<^ 25ul) >>^ 23ul));
	s.(i+.size 7) <- I16.(uint8_to_int16 UI8.(skj7 >>^ 7ul) |^ ((int8_to_int16 (uint8_to_int8 skj8)) <<^ 1ul));

        jBuf.(size 0) <- j +. size 9;
	iBuf.(size 0) <- i +. size 8
    );

    iBuf.(size 0) <- size 0;
    while
    #(fun h -> live h e /\ live h sk /\ live h iBuf /\ live h jBuf)
    #(fun _ h -> live h e /\ live h sk /\ live h iBuf /\ live h jBuf)
    (fun _ -> iBuf.(size 0) <. params_n)
    (fun _ ->
        let i = iBuf.(size 0) in
	let j = jBuf.(size 0) in

        let skj0 = sk.(j+.size 0) in    let skj1 = sk.(j+.size 1) in
	let skj2 = sk.(j+.size 2) in    let skj3 = sk.(j+.size 3) in
	let skj4 = sk.(j+.size 4) in    let skj5 = sk.(j+.size 5) in
	let skj6 = sk.(j+.size 6) in    let skj7 = sk.(j+.size 7) in
	let skj8 = sk.(j+.size 8) in

        e.(i+.size 0) <- I16.(uint8_to_int16 skj0               |^ int32_to_int16 I32.(((uint8_to_int32 skj1) <<^ 31ul) >>^ 23ul));
	e.(i+.size 1) <- I16.(uint8_to_int16 UI8.(skj1 >>^ 1ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj2) <<^ 30ul) >>^ 23ul));
	e.(i+.size 2) <- I16.(uint8_to_int16 UI8.(skj2 >>^ 2ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj3) <<^ 29ul) >>^ 23ul));
	e.(i+.size 3) <- I16.(uint8_to_int16 UI8.(skj3 >>^ 3ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj4) <<^ 28ul) >>^ 23ul));
	e.(i+.size 4) <- I16.(uint8_to_int16 UI8.(skj4 >>^ 4ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj5) <<^ 27ul) >>^ 23ul));
	e.(i+.size 5) <- I16.(uint8_to_int16 UI8.(skj5 >>^ 5ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj6) <<^ 26ul) >>^ 23ul));
	e.(i+.size 6) <- I16.(uint8_to_int16 UI8.(skj6 >>^ 6ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj7) <<^ 25ul) >>^ 23ul));
	e.(i+.size 7) <- I16.(uint8_to_int16 UI8.(skj7 >>^ 7ul) |^ ((int8_to_int16 (uint8_to_int8 skj8)) <<^ 1ul));

        jBuf.(size 0) <- j +. size 9;
	iBuf.(size 0) <- i +. size 8
    );

    copy seeds (sub sk (size 2 *. params_s_bits *. params_n /. size 8) (size 2 *. crypto_seedbytes));

    pop_frame()

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

        pt (i)          (tj               |^ (tj1  <<^ 24ul)); 
	pt (i+.size 1)  ((tj1  >>^  8ul)  |^ (tj2  <<^ 16ul));
	pt (i+.size 2)  ((tj2  >>^ 16ul)  |^ (tj3  <<^  8ul));
	
        jBuf.(size 0) <- j +. size 4;
	iBuf.(size 0) <- i +. params_q_log /. size 8
    );

    assert(v params_k = 1);

    update_sub #MUT #_ #_ pk (params_n *. params_q_log /. size 8) crypto_seedbytes seedA;
    
    pop_frame()

private inline_for_extraction noextract
val decode_pk_pt:
    pk : lbuffer uint8 crypto_publickeybytes
  -> j : size_t{j <. crypto_publickeybytes /. size UI32.n /. size 8}
  -> Stack UI32.t
    (requires fun h -> live h pk)
    (ensures fun h0 _ h1 -> h0 == h1)

let decode_pk_pt pk j =
    uint_from_bytes_le #U32 #_ (sub pk (j *. size UI32.n /. size 8) (size UI32.n /. size 8))

val decode_pk:
    pk : lbuffer I32.t (params_n)
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
    let mask24:UI32.t = UI32.((1ul <<^ params_q_log) -^ 1ul) in

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
	// Lifting the calculation into a let of type UI32.t and then passing it to uint32_to_int32 works at the
	// expense of junking up the code.
        [@inline_let] let u2i = uint32_to_int32 in
	// In the reference code, assignment is done to pp, and "pp = (uint32_t*)pk". Here instead we inline the
	// cast of the reuslt from uint32_t to int32_t in each assignment and then assign directly to elements of pk.
        let ppi = UI32.( (pt j) &^ mask24 ) in pk.(i) <- u2i ppi;
	let ppi1 = UI32.( (((pt j           ) >>^ 24ul) |^ ((pt (j+.size  1))) <<^  8ul) &^ mask24 ) in pk.(i+.size 1) <- u2i ppi1;
	let ppi2 = UI32.( (((pt (j+.size  1)) >>^ 16ul) |^ ((pt (j+.size  2))) <<^ 16ul) &^ mask24 ) in pk.(i+.size 2) <- u2i ppi2;
	let ppi3 = UI32.(   (pt (j+.size  2)  >>^  8ul) ) in pk.(i+.size  3) <- u2i ppi3;

        jBuf.(size 0) <- j +. size 3;
	iBuf.(size 0) <- i +. size 4
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

        pt i            UI32.( ((t_ j)                        &^ ((1ul <<^ 22ul) -^ 1ul)) |^ ((t_ (j+.size  1)) <<^ 22ul) );
	pt (i+.size  1) UI32.( (((t_ (j +.size  1)) >>^ 10ul) &^ ((1ul <<^ 12ul) -^ 1ul)) |^ ((t_ (j+.size  2)) <<^ 12ul) );
	pt (i+.size  2) UI32.( (((t_ (j +.size  2)) >>^ 20ul) &^ ((1ul <<^  2ul) -^ 1ul)) |^ (((t_ (j+.size  3)) &^ ((1ul <<^ 22ul) -^ 1ul)) <<^  2ul) |^ ((t_ (j+.size  4)) <<^ 24ul) );
	pt (i+.size  3) UI32.( (((t_ (j +.size  4)) >>^  8ul) &^ ((1ul <<^ 14ul) -^ 1ul)) |^ ((t_ (j+.size  5)) <<^ 14ul) );
	pt (i+.size  4) UI32.( (((t_ (j +.size  5)) >>^ 18ul) &^ ((1ul <<^  4ul) -^ 1ul)) |^ (((t_ (j+.size  6)) &^ ((1ul <<^ 22ul) -^ 1ul)) <<^  4ul) |^ ((t_ (j+.size  7)) <<^ 26ul) );
	pt (i+.size  5) UI32.( (((t_ (j +.size  7)) >>^  6ul) &^ ((1ul <<^ 16ul) -^ 1ul)) |^ ((t_ (j+.size  8)) <<^ 16ul) );
	pt (i+.size  6) UI32.( (((t_ (j +.size  8)) >>^ 16ul) &^ ((1ul <<^  6ul) -^ 1ul)) |^ (((t_ (j+.size  9)) &^ ((1ul <<^ 22ul) -^ 1ul)) <<^  6ul) |^ ((t_ (j+.size 10)) <<^ 28ul) );
	pt (i+.size  7) UI32.( (((t_ (j +.size 10)) >>^  4ul) &^ ((1ul <<^ 18ul) -^ 1ul)) |^ ((t_ (j+.size 11)) <<^ 18ul) );
	pt (i+.size  8) UI32.( (((t_ (j +.size 11)) >>^ 14ul) &^ ((1ul <<^  8ul) -^ 1ul)) |^ (((t_ (j+.size 12)) &^ ((1ul <<^ 22ul) -^ 1ul)) <<^  8ul) |^ ((t_ (j+.size 13)) <<^ 30ul) );
	pt (i+.size  9) UI32.( (((t_ (j +.size 13)) >>^  2ul) &^ ((1ul <<^ 20ul) -^ 1ul)) |^ ((t_ (j+.size 14)) <<^ 20ul) );
	pt (i+.size 10) UI32.( (((t_ (j +.size 14)) >>^ 12ul) &^ ((1ul <<^ 10ul) -^ 1ul)) |^ ((t_ (j+.size 15)) <<^ 10ul) );

        jBuf.(size 0) <- j +. size 16;
	iBuf.(size 0) <- i +. params_d /. size 2
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
	let ptj10 = pt (j+.size 10) in
	
        z.(i)          <- i2e I32.( ((u2i ptj0) <<^ 10ul) >>^ 10ul );
        z.(i+.size  1) <- i2e I32.( u2i UI32.( ptj0 >>^ 22ul ) |^ (u2i UI32.(ptj1 <<^ 20ul)) >>^ 10ul );
        z.(i+.size  2) <- i2e I32.( u2i UI32.( ptj1 >>^ 12ul ) |^ (u2i UI32.(ptj2 <<^ 30ul)) >>^ 10ul );
        z.(i+.size  3) <- i2e I32.( u2i UI32.( ptj2 <<^  8ul ) >>^ 10ul );
        z.(i+.size  4) <- i2e I32.( u2i UI32.( ptj2 >>^ 24ul ) |^ (u2i UI32.(ptj3 <<^ 18ul)) >>^ 10ul );
        z.(i+.size  5) <- i2e I32.( u2i UI32.( ptj3 >>^ 14ul ) |^ (u2i UI32.(ptj4 <<^ 28ul)) >>^ 10ul );
        z.(i+.size  6) <- i2e I32.( u2i UI32.( ptj4 <<^  6ul ) >>^ 10ul );
        z.(i+.size  7) <- i2e I32.( u2i UI32.( ptj4 >>^ 26ul ) |^ (u2i UI32.(ptj5 <<^ 16ul)) >>^ 10ul );
        z.(i+.size  8) <- i2e I32.( u2i UI32.( ptj5 >>^ 16ul ) |^ (u2i UI32.(ptj6 <<^ 26ul)) >>^ 10ul );
        z.(i+.size  9) <- i2e I32.( u2i UI32.( ptj6 <<^  4ul ) >>^ 10ul );
        z.(i+.size 10) <- i2e I32.( u2i UI32.( ptj6 >>^ 28ul ) |^ (u2i UI32.(ptj7 <<^ 14ul)) >>^ 10ul );
        z.(i+.size 11) <- i2e I32.( u2i UI32.( ptj7 >>^ 18ul ) |^ (u2i UI32.(ptj8 <<^ 24ul)) >>^ 10ul );
        z.(i+.size 12) <- i2e I32.( u2i UI32.( ptj8 <<^  2ul ) >>^ 10ul );
        z.(i+.size 13) <- i2e I32.( u2i UI32.( ptj8 >>^ 30ul ) |^ (u2i UI32.(ptj9 <<^ 12ul)) >>^ 10ul );
        z.(i+.size 14) <- i2e I32.( u2i UI32.( ptj9 >>^ 20ul ) |^ (u2i UI32.(ptj10 <<^ 22ul)) >>^ 10ul );
	z.(i+.size 15) <- i2e I32.( u2i ptj10 >>^ 10ul );

        jBuf.(size 0) <- j +. size 11;
	iBuf.(size 0) <- i +. size 16
    );

    copy c (sub sm (params_n *. params_d /. size 8) crypto_c_bytes);

    pop_frame()
