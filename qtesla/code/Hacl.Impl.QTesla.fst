module Hacl.Impl.QTesla

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

module I = FStar.Int
module I8 = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64
module UI8 = FStar.UInt8
module UI16 = FStar.UInt16
module UI32 = FStar.UInt32
module UI64 = FStar.UInt64
open FStar.Int.Cast

//open LowStar.BufferOps
open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open C.Loops
module LL = Lib.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Platform
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals
open Hacl.Impl.QTesla.Pack
open Hacl.Impl.QTesla.Poly
open Hacl.Impl.QTesla.Gauss

module B  = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

module Seq = FStar.Seq
module LibSeq = Lib.Sequence

module SHA3 = Hacl.SHA3
//module S    = Spec.QTesla

module R    = Hacl.QTesla.Random

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

private let _RADIX32 = size params_radix32

// Reference implementation returns the unsigned version of the element type. Not sure yet whether or not
// it's important to do this. In one case the return value is compared against a quantity that isn't even close
// to exceeding the maximum value of a signed int32, much less an int64, and in all other cases ends up getting
// immediately cast back into a signed type.
val abs_: value: I32.t -> Tot I32.t
let abs_ value = 
    assert_norm(v (_RADIX32 -. size 1) < I32.n);
    let mask = I32.(value >>^ (_RADIX32 -. size 1)) in
    assume(FStar.Int.fits (elem_v (mask ^^ value) - elem_v mask) I32.n);
    I32.((mask ^^ value) -^ mask)

val check_ES:
    p: poly
  -> bound: UI32.t
  -> Stack bool
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 -> modifies0 h0 h1)

let check_ES p bound =
  push_frame();
  // TODO/HACK: This is a hack to bind the hat operators in this function to the appropriate type;
  // heuristic parameter sets use I32.t and provable parameter sets use I16.t. We load the one
  // set of names from the Params module and rebind the operators here. Look into using FStar.Integers
  // to make this less miserable.
  [@inline_let] let op_Plus_Hat = I32.op_Plus_Hat in
  [@inline_let] let op_Subtraction_Hat = I32.op_Subtraction_Hat in
  [@inline_let] let op_Greater_Greater_Hat = I32.op_Greater_Greater_Hat in
  [@inline_let] let op_Amp_Hat = I32.op_Amp_Hat in
  [@inline_let] let op_Bar_Hat = I32.op_Bar_Hat in
  [@inline_let] let lognot = I32.lognot in
  
  let sum = create (size 1) 0ul in
  let limit = create (size 1) params_n in
  let temp = create (size 1) 0l in
  let mask = create (size 1) 0l in
  let list = create params_n 0l in
  let h0 = ST.get () in
  for (size 0) params_n
      (fun h _ -> live h p /\ live h list /\ modifies1 list h0 h)
      (fun j ->
        let pj = p.(j) in
        let abspj = abs_ (elem_to_int32 pj) in
        list.(j) <- abspj
      );

  let h1 = ST.get () in
  for (size 0) params_h
      (fun h _ -> live h p /\ live h sum /\ live h limit /\ live h temp /\ live h mask /\ live h list /\
               modifies (loc mask |+| loc temp |+| loc list |+| loc sum |+| loc limit) h1 h /\
               v (bget h limit 0) <= v params_n)
      (fun j ->
          let loopMax = (limit.(size 0)) -. size 1 in
          let h2 = ST.get () in
          for 0ul loopMax
          (fun h _ -> live h p /\ live h sum /\ live h limit /\ live h temp /\ live h mask /\ live h list /\
                   modifies3 mask temp list h2 h /\ v (bget h limit 0) <= v params_n)
          (fun i ->
              let h3 = ST.get () in
              assume(v i < v params_n - 1);
              assume(FStar.Int.fits (I32.v (bget h3 list (v i + 1)) - I32.v (bget h3 list (v i))) I32.n);
              assert_norm(v (_RADIX32 -. size 1) < 32);
              mask.(size 0) <- ((list.(i +. size 1)) -^ (list.(i))) >>^ (_RADIX32 -. size 1);
              temp.(size 0) <- ((list.(i +. size 1)) &^ (mask.(size 0))) |^
                                    ((list.(i)) &^ (lognot mask.(size 0)));
              list.(i +. size 1) <- (list.(i)) &^ mask.(size 0) |^
                                   (list.(i +. (size 1))) &^ (lognot mask.(size 0));
              list.(i) <- temp.(size 0)
          ); 

          let listIndex = limit.(size 0) -. size 1 in
          let h4 = ST.get () in
          assume(v ((bget h4 limit 0) -. size 1) < v params_n);
          let listAmt = list.(listIndex) in
          let h5 = ST.get () in
          assume(FStar.UInt.fits (UI32.v (bget h5 sum 0) + UI32.v (int32_to_uint32 listAmt)) UI32.n);
          sum.(size 0) <- UI32.(sum.(size 0) +^ int32_to_uint32 listAmt);
          limit.(size 0) <- limit.(size 0) -. size 1
      );

   let sumAmt:UI32.t = sum.(size 0) in
   let res = UI32.(sumAmt >^ bound) in
   pop_frame();
   res

#reset-options "--z3rlimit 300 --max_fuel 1 --max_ifuel 1"// --print_z3_statistics --log_queries --query_stats"

private inline_for_extraction noextract
val poly_uniform_valFromBuffer:
    pos: lbuffer size_t (size 1)
  -> buf: lbuffer uint8 (shake128_rate *. params_genA)
  -> mask: uint32
  -> Stack pub_uint32
    (requires fun h -> live h pos /\ live h buf /\ disjoint pos buf /\
                    v (bget h pos 0) + numbytes U32 <= v (shake128_rate *. params_genA))
    (ensures fun h0 _ h1 -> modifies2 pos buf h0 h1)

let poly_uniform_valFromBuffer pos buf mask =
    push_frame();
    let nbytes:size_t = (params_q_log +. 7ul) /. 8ul in    
    let pos0 = pos.(size 0) in
    let subbuff = sub buf pos0 (size (numbytes U32)) in
    let bufPosAsUint:uint32 = uint_from_bytes_le subbuff in
    let val1:uint32 = bufPosAsUint &. mask in
    pos.(size 0) <- pos0 +. nbytes;
    pop_frame();
    // It is safe to compare this value with the regular less-than operator, so we declassify it to do that.
    unsafe_declassify val1

private inline_for_extraction noextract
val poly_uniform_setA:
    a: poly
  -> iBuf: lbuffer size_t (size 1)
  -> value: pub_uint32
  -> Stack unit
    (requires fun h -> live h a /\ live h iBuf /\ disjoint a iBuf /\
                    ((v value < elem_v params_q /\ v (bget h iBuf 0) < (v params_k * v params_n)) ==>
                    FStar.Int.fits (v value * I64.v params_r2_invn * I64.v params_qinv) I64.n))
    (ensures fun h0 _ h1 -> modifies2 a iBuf h0 h1 /\ 
                         ((v value < elem_v params_q /\ v (bget h0 iBuf 0) < (v params_k * v params_n)) ==>
                          v (bget h1 iBuf 0) = v (bget h0 iBuf 0) + 1))

let poly_uniform_setA a iBuf value =
    push_frame();
    [@inline_let] let params_q = elem_to_uint32 params_q in
    let i = iBuf.(size 0) in
    if (value <. params_q && i <. (params_k *. params_n))
    then ( a.(i) <- reduce I64.((uint32_to_int64 value) *^ params_r2_invn);
           iBuf.(size 0) <- i +. size 1 )
    else ();
    pop_frame()

val poly_uniform:
    a: poly
  -> seed: lbuffer uint8 crypto_randombytes
  -> Stack unit
    (requires fun h -> live h a /\ live h seed /\ disjoint a seed)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)
    
let poly_uniform a seed =
    push_frame();
    let pos = create (size 1) (size 0) in
    let i = create (size 1) (size 0) in
    let nbytes:size_t = (params_q_log +. 7ul) /. 8ul in
    let nblocks = create (size 1) params_genA in
    let mask:uint32 = (u32 1 <<. params_q_log) -. u32 1 in
    let buf = create (shake128_rate *. params_genA) (u8 0) in
    let dmsp = create (size 1) (u16 0) in
    cshake128_qtesla crypto_randombytes seed (dmsp.(size 0)) (shake128_rate *. params_genA) buf;
    dmsp.(size 0) <- dmsp.(size 0) +. (u16 1);

    let h0 = ST.get () in
    LL.while
        (fun h -> live h a /\ live h pos /\ live h i /\ live h nblocks /\ live h buf /\ live h dmsp /\ live h seed /\
               modifies (loc dmsp |+| loc pos |+| loc a |+| loc i |+| loc nblocks |+| loc buf) h0 h)
        (fun h -> v (bget h i 0) < v params_k * v params_n)
        (fun _ -> i.(size 0) <. (params_k *. params_n) )
        (fun _ ->
            if (pos.(size 0)) >. (shake128_rate *. (nblocks.(size 0))) -. ((size 4) *. nbytes)
            then ( nblocks.(size 0) <- size 1;
	         let bufSize:size_t = shake128_rate *. nblocks.(size 0) in
                 let subbuff = sub buf (size 0) bufSize in
                 cshake128_qtesla crypto_randombytes seed dmsp.(size 0) bufSize subbuff;
                 dmsp.(size 0) <- dmsp.(size 0) +. u16 1;
                 pos.(size 0) <- size 0 )
            else ();

            let h1 = ST.get () in assume(v (bget h1 pos 0) + numbytes U32 <= v (shake128_rate *. params_genA));
            let val1 = poly_uniform_valFromBuffer pos buf mask in
            let h1 = ST.get () in assume(v (bget h1 pos 0) + numbytes U32 <= v (shake128_rate *. params_genA));
            let val2 = poly_uniform_valFromBuffer pos buf mask in
            let h1 = ST.get () in assume(v (bget h1 pos 0) + numbytes U32 <= v (shake128_rate *. params_genA));
            let val3 = poly_uniform_valFromBuffer pos buf mask in
            let h1 = ST.get () in assume(v (bget h1 pos 0) + numbytes U32 <= v (shake128_rate *. params_genA));
            let val4 = poly_uniform_valFromBuffer pos buf mask in

            assume(FStar.Int.fits (UI32.v val1 * I64.v params_r2_invn * Int64.v params_qinv) I64.n);
            poly_uniform_setA a i val1;
            assume(FStar.Int.fits (UI32.v val2 * I64.v params_r2_invn * Int64.v params_qinv) I64.n);
            poly_uniform_setA a i val2;
            assume(FStar.Int.fits (UI32.v val3 * I64.v params_r2_invn * Int64.v params_qinv) I64.n);
            poly_uniform_setA a i val3;
            assume(FStar.Int.fits (UI32.v val4 * I64.v params_r2_invn * Int64.v params_qinv) I64.n);
            poly_uniform_setA a i val4
        );

    pop_frame()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

private inline_for_extraction noextract
let randomness_extended_size = (params_k +. size 3) *. crypto_seedbytes

private inline_for_extraction noextract
val qtesla_keygen_sample_gauss_poly:
    randomness_extended: lbuffer uint8 randomness_extended_size
  -> nonce: lbuffer uint32 (size 1)
  -> p: poly
  -> k: size_t{v k <= v params_k}
  -> Stack unit
    (requires fun h -> live h randomness_extended /\ live h nonce /\ live h p /\ 
                    disjoint randomness_extended nonce /\ disjoint randomness_extended p /\ disjoint nonce p)
    (ensures fun h0 _ h1 -> modifies2 nonce p h0 h1)

let qtesla_keygen_sample_gauss_poly randomness_extended nonce p k =
    let subbuffer = sub randomness_extended (k *. crypto_seedbytes) crypto_randombytes in
    let nonce0 = nonce.(size 0) in
    nonce.(size 0) <- nonce0 +. u32 1;
    let nonce1 = nonce.(size 0) in
    sample_gauss_poly p subbuffer nonce1

(*let test (e:poly_k) (k:size_t{v k < v params_k}) : Stack unit (requires fun h -> live h e) (ensures fun _ _ _ -> True) =
    //let ek = sub e (k *. params_n) params_n in
    let ek2 = index_poly e k in
    //assert(loc_includes (loc e) (loc ek));
    assert(loc_includes (loc e) (loc ek2))*)

private inline_for_extraction noextract
val qtesla_keygen_:
    randomness: lbuffer uint8 crypto_randombytes
  -> pk: lbuffer uint8 crypto_publickeybytes
  -> sk: lbuffer uint8 crypto_secretkeybytes
  -> Stack (r:I32.t{r == 0l})
    (requires fun h -> live h randomness /\ live h pk /\ live h sk /\ 
                    disjoint randomness pk /\ disjoint randomness sk /\ disjoint pk sk)
    (ensures fun h0 _ h1 -> modifies2 pk sk h0 h1)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"
let qtesla_keygen_ randomness pk sk =
  push_frame();
  let randomness_extended = create randomness_extended_size (u8 0) in
  let e:poly_k = poly_k_create () in
  let s:poly = poly_create () in
  let s_ntt:poly = poly_create () in
  let a:poly_k = poly_k_create () in
  let t:poly_k = poly_k_create () in 
  let nonce = create (size 1) (u32 0) in
  params_SHAKE crypto_randombytes randomness randomness_extended_size randomness_extended;
  let h0 = ST.get () in
  for (size 0) params_k
      (fun h _ -> live h nonce /\ live h e /\ live h randomness_extended /\ modifies2 nonce e h0 h)
      (fun k ->
        do_while
          (fun h _ -> live h nonce /\ live h e /\ live h randomness_extended /\ modifies2 nonce e h0 h)
          (fun _ ->
            let ek = index_poly e k in
            qtesla_keygen_sample_gauss_poly randomness_extended nonce ek k;
            not (check_ES ek params_Le)
          )
      ); 
  let h1 = ST.get () in
  do_while
      (fun h stop -> live h s /\ live h randomness_extended /\ live h nonce /\ modifies2 nonce s h1 h)
      (fun _ ->
        qtesla_keygen_sample_gauss_poly randomness_extended nonce s params_k;
        not (check_ES s params_Ls)
      ); 
  let h2 = ST.get () in
  let rndsubbuffer = sub randomness_extended ((params_k +. (size 1)) *. crypto_seedbytes) (size 2 *. crypto_seedbytes) in
  poly_uniform a (sub rndsubbuffer (size 0) crypto_randombytes);
  let h3 = ST.get () in

  poly_ntt s_ntt s;
  let h4 = ST.get () in
  C.Loops.for (size 0) params_k
      (fun h _ -> live h t /\ live h a /\ live h s_ntt /\ live h e /\ modifies1 t h4 h)
      (fun k ->
          let tk:poly = index_poly t k in
          let ak:poly = index_poly a k in
          let ek:poly = index_poly e k in
          poly_mul tk ak s_ntt;
          poly_add_correct tk tk ek
        );

  let h5 = ST.get () in
  encode_or_pack_sk sk s e rndsubbuffer;
  let h6 = ST.get () in
  encode_pk pk t (sub rndsubbuffer (size 0) crypto_seedbytes);
  let h7 = ST.get () in
  pop_frame(); //admit();
  0l

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val qtesla_keygen:
    pk: lbuffer uint8 crypto_publickeybytes
  -> sk: lbuffer uint8 crypto_secretkeybytes
  -> Stack (r:I32.t{r == 0l})
    (requires fun h -> live h pk /\ live h sk /\ 
                    disjoint R.state pk /\ disjoint R.state sk /\ disjoint pk sk)
    (ensures fun h0 _ h1 -> modifies3 R.state pk sk h0 h1)

let qtesla_keygen pk sk =
    recall R.state;
    push_frame();
    let randomness = create crypto_randombytes (u8 0) in
    R.randombytes_ crypto_randombytes randomness;
    let r = qtesla_keygen_ randomness pk sk in
    pop_frame();
    r

val sample_y:
    y : poly
  -> seed : lbuffer uint8 crypto_randombytes
  -> nonce: I32.t
  -> Stack unit
    (requires fun h -> live h y /\ live h seed /\ disjoint y seed)
    (ensures fun h0 _ h1 -> modifies1 y h0 h1)

let sample_y y seed nonce =
    push_frame();

    let nblocks_shake = shake_rate /. (((params_b_bits +. (size 1)) +. (size 7)) /. (size 8)) in
    let bplus1bytes = ((params_b_bits +. size 1) +. (size 7)) /. (size 8) in

    let i = create (size 1) (size 0) in
    let pos = create (size 1) (size 0) in
    let nblocks = create (size 1) params_n in
    let buf = create (params_n *. bplus1bytes ) (u8 0) in
    let nbytes = bplus1bytes in
    [@inline_let] let dmspVal:uint16 = cast U16 SEC (Lib.RawIntTypes.u16_from_UInt16 (int32_to_uint16 I32.(nonce <<^ 8ul))) in
    let dmsp = create (size 1) dmspVal in

    params_cSHAKE crypto_randombytes seed dmsp.(size 0) (params_n *. nbytes) buf;
    let hInit = ST.get () in
    assume(v (bget hInit dmsp 0) < pow2 ((bits U16) - 1));
    dmsp.(size 0) <- dmsp.(size 0) +. u16 1;

    let h0 = ST.get () in
    LL.while
    (fun h -> live h y /\ live h i /\ live h pos /\ live h nblocks /\ live h buf /\ live h dmsp /\
           modifies (loc y |+| loc i |+| loc pos |+| loc nblocks |+| loc buf |+| loc dmsp) h0 h)
    (fun h -> v (bget h i 0) < v params_n)
    (fun _ -> i.(size 0) <. params_n)
    (fun _ ->
        if pos.(size 0) >=. nblocks.(size 0) *. nbytes
	then (
	    nblocks.(size 0) <- nblocks_shake;
	    params_cSHAKE crypto_randombytes seed dmsp.(size 0) shake_rate (sub buf (size 0) shake_rate);
            assume(v (bget hInit dmsp 0) < pow2 ((bits U16) - 1));
	    dmsp.(size 0) <- dmsp.(size 0) +. u16 1;
	    pos.(size 0) <- size 0
	) else ();

        let pos0 = pos.(size 0) in
        assume(v pos0 + numbytes U32 <= v (params_n *. bplus1bytes));
	let subbuff = sub buf pos0 (size (numbytes U32)) in
	let bufPosAsU32 = uint_from_bytes_le #U32 #_ subbuff in
	let bufPosAsElem = uint32_to_elem (Lib.RawIntTypes.u32_to_UInt32 bufPosAsU32) in
	let i0 = i.(size 0) in
	// Heuristic parameter sets do four at once. Perf. But optional.
        let h1 = ST.get () in
        assume(FStar.Int.fits (elem_v (to_elem 1 <<^ (params_b_bits +. size 1)) - 1) elem_n);
        assume(is_elem (bufPosAsElem &^ ((to_elem 1 <<^ (params_b_bits +. size 1)) -^ to_elem 1)));
	y.(i0) <- bufPosAsElem &^ ((to_elem 1 <<^ (params_b_bits +. size 1)) -^ to_elem 1);
        let h2 = ST.get () in
        assume(is_elem ((bget h2 y (v i0)) -^ params_B));
	y.(i0) <- y.(i0) -^ params_B;
	if y.(i0) <> (to_elem 1 <<^ params_b_bits)
	then ( i.(size 0) <- i0 +. size 1 )
	else ();
	pos.(size 0) <- pos.(size 0) +. nbytes
    );

    pop_frame()
    
val hash_H:
    c_bin : lbuffer uint8 crypto_c_bytes
  -> v : poly_k
  -> hm : lbuffer uint8 crypto_hmbytes
  -> Stack unit
    (requires fun h -> live h c_bin /\ live h v /\ live h hm /\ disjoint c_bin v /\ disjoint c_bin hm /\ disjoint v hm)
    (ensures fun h0 _ h1 -> modifies1 c_bin h0 h1)

let hash_H c_bin v_ hm =
    push_frame();

    [@inline_let] let params_q = elem_to_int32 params_q in
    let t = create (params_k *. params_n +. crypto_hmbytes) (u8 0) in

    let h0 = ST.get () in
    for 0ul params_k
    (fun h _ -> live h v_ /\ live h t /\ modifies1 t h0 h)
    (fun k ->
        push_frame();
        let index = create (size 1) (k *. params_n) in
        let h1 = ST.get () in
	for 0ul params_n
	(fun h i -> live h v_ /\ live h t /\ live h index /\ modifies2 t index h1 h) ///\ 
                 //(i < v params_n ==> v (bget h index 0) < v (k *. params_n +. params_n)))
	(fun i ->
	    let vindex:elem = v_.(index.(size 0)) in
	    let temp:I32.t = elem_to_int32 vindex in
            assert_norm(v (_RADIX32 -. size 1) < I32.n);
	    let mask = I32.((params_q /^ 2l -^ temp) >>^ (_RADIX32 -. size 1)) in
	    let temp = I32.(((temp -^ params_q) &^ mask) |^ (temp &^ (lognot mask))) in
            assume(FStar.Int.fits (I32.v (1l <<^ params_d) - 1) I32.n);
	    let cL = I32.(temp &^ ((1l <<^ params_d) -^ 1l)) in
            assert_norm(v (params_d -. size 1) < I32.n);
            assume(FStar.Int.fits (I32.v ((1l <<^ (params_d -. (size 1)))) - I32.v cL) I32.n);
	    let mask = I32.(((1l <<^ (params_d -. (size 1))) -^ cL) >>^ (_RADIX32 -. size 1)) in
            assume(FStar.Int.fits (I32.v cL - (I32.v (1l <<^ params_d))) I32.n);
	    let cL = I32.(((cL -^ (1l <<^ params_d)) &^ mask) |^ (cL &^ (lognot mask))) in
            assume(FStar.Int.fits (I32.v temp - I32.v cL) I32.n);
	    t.(index.(size 0)) <- Lib.RawIntTypes.u8_from_UInt8 (int32_to_uint8 I32.((temp -^ cL) >>^ params_d));
	    // Putting (index.(size 0)) inline in the assignment causes a typing error for some reason.
	    // Opened a bug on this.
	    let indexVal:size_t = index.(size 0) in
            assume(v indexVal + 1 < v (k *. params_n +. params_n));
	    index.(size 0) <- indexVal +. (size 1)
	);
        pop_frame()
    );

    update_sub #MUT #_ #_ t (params_k *. params_n) crypto_hmbytes hm;
    params_SHAKE (params_k *. params_n +. crypto_hmbytes) t crypto_c_bytes c_bin;

    pop_frame()

val encode_c:
    pos_list : lbuffer UI32.t params_h
  -> sign_list : lbuffer I16.t params_h
  -> c_bin : lbuffer uint8 crypto_c_bytes
  -> Stack unit
    (requires fun h -> live h pos_list /\ live h sign_list /\ live h c_bin /\ disjoint pos_list sign_list /\
                    disjoint pos_list c_bin /\ disjoint sign_list c_bin)
    (ensures fun h0 _ h1 -> modifies2 pos_list sign_list h0 h1)

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

// This function looks identical between the I and p-III sets.
let encode_c pos_list sign_list c_bin =
    push_frame();

    let c = create params_n 0s in
    let r = create shake128_rate (u8 0) in
    let dmsp = create (size 1) (u16 0) in
    let cnt = create (size 1) (size 0) in
    let i = create (size 1) (size 0) in

    cshake128_qtesla crypto_randombytes c_bin (dmsp.(size 0)) shake128_rate r;
    let dmspVal:uint16 = dmsp.(size 0) in
    dmsp.(size 0) <- dmspVal +. (u16 1);

    // c already initialized to zero above, no need to loop and do it again

    let h0 = ST.get () in
    LL.while
    (fun h -> live h pos_list /\ live h sign_list /\ live h c_bin /\ live h c /\ live h r /\ live h dmsp /\ live h cnt /\ live h i /\
           modifies (loc r |+| loc dmsp |+| loc cnt |+| loc c |+| loc pos_list |+| loc sign_list |+| loc i) h0 h)
    (fun h -> v (bget h i 0) < v params_h)
    (fun _ -> i.(size 0) <. params_h)
    (fun _ ->
        let iVal:size_t = i.(size 0) in
        if cnt.(size 0) >. (shake128_rate -. (size 3))
	then ( cshake128_qtesla crypto_randombytes c_bin (dmsp.(size 0)) shake128_rate r;
	       dmsp.(size 0) <- dmsp.(size 0) +. (u16 1);
               cnt.(size 0) <- size 0
	     )
	else ();

        let cntVal:size_t = cnt.(size 0) in
        let rCntVal:uint8 = r.(cntVal) in
        [@inline_let] let rCntVal:size_t = unsafe_declassify (cast U32 SEC rCntVal) in
        let rCntVal1:uint8 = r.(cntVal +. size 1) in
        [@inline_let] let rCntVal1:size_t = unsafe_declassify (cast U32 SEC rCntVal1) in
	let pos:size_t = (rCntVal <<. size 8) |. rCntVal1 in
	let pos:size_t = pos &. (params_n -. (size 1)) in

        assume(v pos < v params_n);
	if (c.(pos)) = 0s
	then ( let rCntVal2:uint8 = r.(cntVal +. size 2) in
               [@inline_let] let rCntVal2:UI8.t = Lib.RawIntTypes.u8_to_UInt8 rCntVal2 in
               if UI8.((rCntVal2 &^ 1uy) = 1uy)
	       then c.(pos) <- -1s
	       else c.(pos) <- 1s;
	       pos_list.(iVal) <- pos;
	       sign_list.(iVal) <- c.(pos);
	       i.(size 0) <- iVal +. (size 1)
	     )
	else ();
	cnt.(size 0) <- cntVal +. (size 3)
    );

    pop_frame()

val sparse_mul:
    prod : poly
  -> s : lbuffer sparse_elem params_n
  -> pos_list : lbuffer UI32.t params_h
  -> sign_list : lbuffer I16.t params_h
  -> Stack unit
    (requires fun h -> live h prod /\ live h s /\ live h pos_list /\ live h sign_list /\ 
                    disjoint prod s /\ disjoint prod pos_list /\ disjoint prod sign_list)
    (ensures fun h0 _ h1 -> modifies1 prod h0 h1)

let sparse_mul prod s pos_list sign_list =
    push_frame();

    let t = s in

    let h0 = ST.get () in
    for 0ul params_n
    (fun h _ -> live h prod /\ modifies1 prod h0 h)
    (fun i -> prod.(i) <- to_elem 0);

    let h1 = ST.get () in
    for 0ul params_h
    (fun h _ -> live h prod /\ live h t /\ live h pos_list /\ live h sign_list /\ modifies1 prod h1 h)
    (fun i ->
        let pos = pos_list.(i) in
        let h2 = ST.get () in
	for 0ul pos
	(fun h _ -> live h prod /\ live h t /\ live h pos_list /\ live h sign_list /\ modifies1 prod h2 h)
	(fun j -> 
	    let sign_list_i:I16.t = sign_list.(i) in
            assume(v (j +. params_n -. pos) < v params_n);
	    let tVal:sparse_elem = t.(j +. params_n -. pos) in
            assume(v j < v params_n);
            assume(FStar.Int.fits (I16.v sign_list_i * I16.v tVal) I16.n);
            let hx = ST.get () in
            assume(FStar.Int.fits (elem_v (bget hx prod (v j)) - (I16.v sign_list_i * I16.v tVal)) elem_n);
            assume(is_elem ((bget hx prod (v j)) -^ (int16_to_elem I16.(sign_list_i *^ (sparse_to_int16 tVal)))));
	    prod.(j) <- prod.(j) -^ (int16_to_elem I16.(sign_list_i *^ (sparse_to_int16 tVal)))
	);

        let h3 = ST.get () in
        assume(v pos < v params_n);
	for pos params_n
	(fun h _ -> live h prod /\ live h t /\ live h pos_list /\ live h sign_list /\ modifies1 prod h3 h)
	(fun j -> 
	    let sign_list_i:I16.t = sign_list.(i) in
	    let tVal:sparse_elem = t.(j -. pos) in
            let hx = ST.get () in
            assume(FStar.Int.fits (I16.v sign_list_i * I16.v tVal) I16.n);
            assume(FStar.Int.fits (elem_v (bget hx prod (v j)) + (I16.v sign_list_i * I16.v tVal)) elem_n);
            assume(is_elem ((bget hx prod (v j)) +^ (int16_to_elem I16.(sign_list_i *^ (sparse_to_int16 tVal)))));
  	    prod.(j) <- prod.(j) +^ (int16_to_elem I16.(sign_list_i *^ (sparse_to_int16 tVal)))
	)
    );

    pop_frame()

val sparse_mul32:
    prod : poly
  -> pk : lbuffer I32.t params_n
  -> pos_list : lbuffer UI32.t params_h
  -> sign_list : lbuffer I16.t params_h
  -> Stack unit
    (requires fun h -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list /\
                    disjoint prod pk /\ disjoint prod pos_list /\ disjoint prod sign_list /\
                    disjoint pk pos_list /\ disjoint pk sign_list /\ disjoint pos_list sign_list /\
                    (forall i . v (bget h pos_list i) < v params_n))
    (ensures fun h0 _ h1 -> modifies1 prod h0 h1)

let sparse_mul32 prod pk pos_list sign_list =
    push_frame();

    let h0 = ST.get () in
    for 0ul params_n
    (fun h _ -> live h prod /\ modifies1 prod h0 h)
    (fun i -> prod.(i) <- to_elem 0);

    let h1 = ST.get () in
    for 0ul params_h
    (fun h _ -> live h prod /\ live h pk /\ live h pos_list /\ live h sign_list /\ modifies1 prod h1 h)
    (fun i ->
        let hPos = ST.get () in
        assert(v (bget hPos pos_list (v i)) < v params_n);
        let pos = pos_list.(i) in
	let sign_list_i = sign_list.(i) in
        let h2 = ST.get () in
	for 0ul pos
	(fun h _ -> live h prod /\ live h pk /\ modifies1 prod h2 h)
	(fun j ->
	    let pkItem = pk.(j +. params_n -. pos) in
            assume(FStar.Int.fits (I16.v sign_list_i * I32.v pkItem) I32.n);
            let hProd = ST.get () in
            assume(FStar.Int.fits (elem_v (bget hProd prod (v j)) - (I16.v sign_list_i * I32.v pkItem)) elem_n);
            assume(is_elem_int (elem_v (bget hProd prod (v j)) - (I16.v sign_list_i * I32.v pkItem)));
	    prod.(j) <- prod.(j) -^ int32_to_elem I32.( (int16_to_int32 sign_list_i) *^ pkItem )
	);
        let h3 = ST.get () in
	for pos params_n
	(fun h _ -> live h prod /\ live h pk /\ modifies1 prod h3 h)
	(fun j ->
	    let pkItem = pk.(j -. pos) in
            assume(FStar.Int.fits (I16.v sign_list_i * I32.v pkItem) I32.n);
            let hProd = ST.get () in
            assume(FStar.Int.fits (elem_v (bget hProd prod (v j)) + (I16.v sign_list_i * I32.v pkItem)) elem_n);
            assume(is_elem_int (elem_v (bget hProd prod (v j)) + (I16.v sign_list_i * I32.v pkItem)));
	    prod.(j) <- prod.(j) +^ int32_to_elem I32.( (int16_to_int32 sign_list_i) *^ pkItem )
	)
    );

    let h4 = ST.get () in
    for 0ul params_n
    (fun h _ -> live h prod /\ modifies1 prod h4 h)
    (fun i -> prod.(i) <- barr_reduce prod.(i));

    pop_frame()

val test_rejection:
    z : poly
  -> Stack bool
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

let test_rejection z =
    [@inline_let] let params_B = elem_to_int32 params_B in
    [@inline_let] let params_U = elem_to_int32 params_U in
    [@inline_let] let op_Subtraction_Hat = I32.op_Subtraction_Hat in
    [@inline_let] let op_Greater_Hat = I32.op_Greater_Hat in

    let h0 = ST.get () in
    let _, res =
    interruptible_for 0ul params_n
    (fun h _ _ -> live h z /\ h0 == h)
    (fun i ->
        let zi:elem = z.(i) in
        let zVal:I32.t = elem_to_int32 zi in
	abs_ zVal >^ params_B -^ params_U
    ) in

    res

val test_correctness:
    v_ : poly
  -> Stack (r:I32.t{r == 0l \/ r == 1l})
    (requires fun h -> live h v_)
    (ensures fun h0 _ h1 -> modifies0 h0 h1)

let test_correctness v_ =
    push_frame();

    let res = create (size 1) 0l in

    let h0 = ST.get () in
    let _, _ = interruptible_for 0ul params_n
    (fun h _ _ -> live h v_ /\ modifies1 res h0 h /\ ((bget h res 0) == 0l \/ (bget h res 0) == 1l))
    (fun i ->
        let h1 = ST.get () in
        assume(is_elem (params_q /^ (to_elem 2) -^ (bget h1 v_ (v i))));
        let mask:elem = (params_q /^ (to_elem 2) -^ v_.(i)) in
        assert_norm(v (_RADIX32 -. size 1) < I32.n);
        let mask:I32.t = I32.((elem_to_int32 mask) >>^ (_RADIX32 -. size 1)) in
        assume(is_elem ((((bget h1 v_ (v i)) -^ params_q) &^ (int32_to_elem mask)) |^ ((bget h1 v_ (v i)) &^ (lognot (int32_to_elem mask)))));
        let val_:elem = (((v_.(i) -^ params_q) &^ (int32_to_elem mask)) |^ (v_.(i) &^ (lognot (int32_to_elem mask)))) in
        let val_:I32.t = elem_to_int32 val_ in
        // From here on, we only use params_q and params_rejection in 32-bit operations, so "cast" them to int32_t.
        [@inline_let] let params_q = elem_to_int32 params_q in
        [@inline_let] let params_rejection = elem_to_int32 params_rejection in
        assume(FStar.Int.fits (I32.v (abs_ val_) - I32.v (params_q /^ 2l -^ params_rejection)) I32.n);
        let t0:UI32.t = UI32.(int32_to_uint32 I32.(((lognot ((abs_ val_) -^ (params_q /^ 2l -^ params_rejection))))) >>^ (_RADIX32 -. size 1)) in
        let left:I32.t = val_ in
        assert_norm(v (params_d -. (size 1)) < I32.n);
        assume(FStar.Int.fits (I32.v val_ + I32.v (1l <<^ (params_d -. (size 1)))) I32.n);
        assume(FStar.Int.fits (I32.v val_ + I32.v (1l <<^ (params_d -. (size 1))) - 1) I32.n);
        let val_:I32.t = I32.((val_ +^ (1l <<^ (params_d -. (size 1))) -^ 1l) >>^ params_d) in
        assume(FStar.Int.fits (I32.v left - I32.v (val_ <<^ params_d)) I32.n);
        let val_:I32.t = I32.(left -^ (val_ <<^ params_d)) in
        assume(FStar.Int.fits (I32.v (1l <<^ (params_d -. (size 1))) - elem_v params_rejection) I32.n);
        assume(FStar.Int.fits (I32.v (abs_ val_) - (I32.v (1l <<^ (params_d -. (size 1))) - elem_v params_rejection)) I32.n);
        let t1:UI32.t = UI32.(int32_to_uint32 I32.(((lognot ((abs_ val_) -^ ((1l <<^ (params_d -. (size 1))) -^ params_rejection))))) >>^ (_RADIX32 -. size 1)) in
        if UI32.((t0 |^ t1) = 1ul)
        then ( res.(size 0) <- 1l; true )
        else ( false )
    ) in

    let resVal:I32.t = res.(size 0) in
    pop_frame();
    resVal

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

val qtesla_sign_do_while:
    randomness: lbuffer uint8 crypto_seedbytes
  -> randomness_input: lbuffer uint8 (crypto_randombytes +. crypto_seedbytes +. crypto_hmbytes)
  -> nonce: lbuffer I32.t (size 1)
  -> a: poly_k
  -> s: lbuffer sparse_elem params_n
  -> e: lbuffer sparse_elem (params_n *. params_k)
  -> smlen : lbuffer size_t 1ul // smlen only valid on output; does _not_ indicate allocated size of sm on input
  -> mlen : size_t
  -> m : lbuffer uint8 mlen
  -> sm: lbuffer uint8 (crypto_bytes +. mlen)
  -> Stack bool
    (requires fun h -> live h randomness /\ live h randomness_input /\ live h nonce /\ live h a /\ live h s /\ live h e /\ 
                    live h smlen /\ live h m /\ live h sm /\

                    disjoint randomness randomness_input /\ disjoint randomness nonce /\ disjoint randomness a /\ 
                    disjoint randomness s /\ disjoint randomness e /\ disjoint randomness smlen /\ disjoint randomness m /\ 
                    disjoint randomness sm /\

                    disjoint randomness_input nonce /\ disjoint randomness_input a /\ disjoint randomness_input s /\
                    disjoint randomness_input e /\ disjoint randomness_input smlen /\ disjoint randomness_input m /\
                    disjoint randomness_input sm /\

                    disjoint nonce a /\ disjoint nonce s /\ disjoint nonce e /\ disjoint nonce smlen /\ disjoint nonce m /\
                    disjoint nonce sm /\

                    disjoint a s /\ disjoint a e /\ disjoint a smlen /\ disjoint a m /\ disjoint a sm /\

                    disjoint s e /\ disjoint s smlen /\ disjoint s m /\ disjoint s sm /\

                    disjoint e smlen /\ disjoint e m /\ disjoint e sm /\

                    disjoint smlen m /\ disjoint smlen sm /\ disjoint m sm /\
                    
                    FStar.Int.fits (I32.v (bget h nonce 0) + 1) I32.n)
    (ensures fun h0 _ h1 -> modifies3 nonce smlen sm h0 h1)

let qtesla_sign_do_while randomness randomness_input nonce a s e smlen mlen m sm =
    push_frame();
    let c = create crypto_c_bytes (u8 0) in
    let pos_list = create params_h 0ul in
    let sign_list = create params_h 0s in
    let y:poly = poly_create () in
    let y_ntt:poly = poly_create () in
    let sc:poly = poly_create () in
    let z:poly = poly_create () in 
    let v_:poly_k = poly_k_create () in 
    let ec:poly_k = poly_k_create () in
    let rsp = create (size 1) 0l in

    nonce.(size 0) <- I32.(nonce.(size 0) +^ 1l);
    sample_y y randomness (nonce.(size 0));
    // TODO: ntt transformation only happens here in provable parameter sets because poly_mul assumes
    // both arguments are in ntt form. Heuristic parameter sets only assume the first parameter is in
    // ntt form.
    poly_ntt y_ntt y;
    let h1 = ST.get () in
    for 0ul params_k
        (fun h _ -> live h v_ /\ live h a /\ live h y_ntt /\ modifies1 v_ h1 h)
        (fun k ->
            poly_mul (index_poly v_ k) (index_poly a k) y_ntt
        );

    hash_H c v_ (sub randomness_input (crypto_randombytes +. crypto_seedbytes) crypto_hmbytes);
    encode_c pos_list sign_list c;
    sparse_mul sc s pos_list sign_list;
    poly_add z y sc;

    let res = 
    if test_rejection z
    then (false)
    else (
         let h2 = ST.get () in
         let _, _ = 
         interruptible_for (size 0) params_k
         (fun h _ _ -> live h ec /\ live h e /\ live h pos_list /\ live h sign_list /\ live h v_ /\ live h rsp /\
                    modifies3 ec v_ rsp h2 h)
         (fun k ->
             let sk_offset:size_t = (params_n *. (k +. (size 1))) in
             let sublen:size_t = crypto_secretkeybytes -. sk_offset in
             sparse_mul (index_poly ec k) (sub e (params_n *. k) params_n) pos_list sign_list;
             poly_sub_correct (index_poly v_ k) (index_poly v_ k) (index_poly ec k);
             rsp.(size 0) <- test_correctness (index_poly v_ k);
             let rspVal = rsp.(size 0) in rspVal <> 0l
         ) in

         if (let rspVal = rsp.(size 0) in rspVal <> 0l)
         then (false)
         else (
              let h3 = ST.get () in
              for 0ul mlen
              (fun h _ -> live h sm /\ live h m /\ modifies1 sm h3 h)
              (fun i -> sm.(crypto_bytes +. i) <- m.(i) );

              smlen.(size 0) <- crypto_bytes +. mlen;

              encode_sig sm c z;

              true
              )
        ) in
    pop_frame(); 
    res

//#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val qtesla_sign:
    smlen : lbuffer size_t 1ul // smlen only valid on output; does _not_ indicate allocated size of sm on input
  -> mlen : size_t
  -> m : lbuffer uint8 mlen
  -> sm: lbuffer uint8 (crypto_bytes +. mlen)
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack unit
    (requires fun h -> live h sm /\ live h m /\ live h sk /\ 
                    disjoint R.state smlen /\ disjoint R.state m /\ disjoint R.state sm /\ disjoint R.state sk /\
                    disjoint smlen m /\ disjoint smlen sm /\ disjoint smlen sk /\
                    disjoint sm m /\ disjoint sm sk /\ disjoint m sk)
    (ensures fun h0 _ h1 -> modifies3 R.state sm smlen h0 h1)

let qtesla_sign smlen mlen m sm sk =
    recall R.state;
    push_frame();

    let randomness = create crypto_seedbytes (u8 0) in
    let randomness_input = create (crypto_randombytes +. crypto_seedbytes +. crypto_hmbytes) (u8 0) in
    let a:poly_k = poly_k_create () in
    let seeds = create (size 2 *. crypto_seedbytes) (u8 0) in
    let (s:lbuffer sparse_elem params_n) = create params_n (to_sparse_elem 0) in
    let e = create (params_n *. params_k) (to_sparse_elem 0) in
    let nonce = create (size 1) 0l in

    decode_sk seeds s e sk;
    
    R.randombytes_ crypto_randombytes (sub randomness_input crypto_randombytes crypto_randombytes);
    update_sub randomness_input (size 0) crypto_seedbytes (sub seeds crypto_seedbytes crypto_seedbytes);
    params_SHAKE mlen m crypto_hmbytes (sub randomness_input (crypto_randombytes +. crypto_seedbytes) crypto_hmbytes);
    params_SHAKE (crypto_randombytes +. crypto_seedbytes +. crypto_hmbytes) randomness_input crypto_seedbytes randomness;

    poly_uniform a (sub seeds (size 0) crypto_randombytes);

    let h0 = ST.get () in
    do_while
        (fun h _ -> live h smlen /\ live h m /\ live h sm /\ live h s /\ live h e /\
                 live h randomness /\ live h randomness_input /\ live h a /\ live h seeds /\ live h nonce /\
                 modifies3 nonce smlen sm h0 h)
        (fun _ -> qtesla_sign_do_while randomness randomness_input nonce a s e smlen mlen m sm);
    pop_frame()

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val test_z:
    z : poly
  -> Stack (r:I32.t{r == 0l \/ r == 1l})
    (requires fun h -> live h z)
    (ensures fun h0 _ h1 -> h0 == h1)

let test_z z =
    let h0 = ST.get () in
    let _ , res = interruptible_for 0ul params_n
    (fun h _ _ -> live h z /\ h0 == h)
    (fun i ->
        let zi = z.(i) in
        zi <^ to_elem (-1) *^ (params_B -^ params_U) || zi >^ (params_B -^ params_U)
    ) in
    if res
    then 1l
    else 0l

val qtesla_verify:
    mallocated : size_t
  -> mlen : lbuffer size_t 1ul
  -> m : lbuffer uint8 mallocated
  -> smlen : size_t
  -> sm : lbuffer uint8 smlen
  -> pk : lbuffer uint8 crypto_publickeybytes
  -> Stack (r:I32.t{r == 0l \/ r == (-1l) \/ r == (-2l) \/ r == (-3l)})
    (requires fun h -> live h m /\ live h mlen /\ live h sm /\ live h pk /\
                    disjoint mlen m /\ disjoint mlen sm /\ disjoint mlen pk /\
                    disjoint m sm /\ disjoint m pk /\
                    disjoint sm pk)
    (ensures fun h0 _ h1 -> modifies2 mlen m h0 h1)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

let qtesla_verify mallocated mlen m smlen sm pk =

    // Can't return from the middle of a function in F*, so instead we use this if-then-else structure where
    // the else is the entire rest of the function after the return statement.
    if smlen <. crypto_bytes then ( -1l ) else (
    push_frame();
    let c = create crypto_c_bytes (u8 0) in
    let c_sig = create crypto_c_bytes (u8 0) in
    let seed = create crypto_seedbytes (u8 0) in
    let hm = create crypto_hmbytes (u8 0) in
    let pos_list = create params_h 0ul in
    let sign_list = create params_h 0s in
    let pk_t = create (params_n *. params_k) 0l in
    let w = poly_k_create () in
    let a = poly_k_create () in
    let tc = poly_k_create () in
    let z = poly_create () in
    let z_ntt = poly_create() in

    decode_sig c z (sub sm (size 0) crypto_bytes); 
    if test_z z <> 0l then ( pop_frame(); -2l ) else (
    decode_pk pk_t seed pk;
    poly_uniform a seed;
    encode_c pos_list sign_list c;
    poly_ntt z_ntt z; 

    let h0 = ST.get () in
    for 0ul params_k
    (fun h _ -> live h w /\ live h a /\ live h z_ntt /\ live h tc /\ live h pk_t /\ live h pos_list /\ live h sign_list /\
             modifies2 w tc h0 h)
    (fun k ->
        poly_mul (index_poly w k) (index_poly a k) z_ntt;
        sparse_mul32 (index_poly tc k) (sub pk_t (k *. params_n) params_n) pos_list sign_list;
        poly_sub_reduce (index_poly w k) (index_poly w k) (index_poly tc k)
    );

    params_SHAKE (smlen -. crypto_bytes) (sub sm crypto_bytes (smlen -. crypto_bytes)) crypto_hmbytes hm;
    hash_H c_sig w hm;

    // lbytes_eq iterates over the entire buffer no matter what, which we don't need. memcmp would be fine since
    // this is all public data. Not yet determined if there's a construct which extracts as memcmp.
    // So we may do unnecessary work but it's still correct.
    if not (lbytes_eq c c_sig) then ( pop_frame(); -3l ) else (
    [@inline_let] let mlenVal = smlen -. crypto_bytes in
    mlen.(size 0) <- mlenVal;
    let h1 = ST.get () in
    for 0ul mlenVal
    (fun h _ -> live h m /\ live h sm /\ modifies1 m h1 h)
    (fun i -> m.(i) <- sm.(crypto_bytes +. i) );

    pop_frame();
    0l
    )))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

/// NIST required API wrappers

// API is identical here. Although defining "let crypto_sign_keypair = qtesla_keygen" causes KreMLin to extract
// crypto_sign_keypair as a function pointer pointing to qtesla_keygen; this way gives us an actual wrapper.
let crypto_sign_keypair pk sk = qtesla_keygen pk sk

val crypto_sign:
    sm : buffer uint8
  -> smlen : lbuffer UI64.t 1ul
  -> m : buffer uint8
  -> mlen : UI64.t{length m = v mlen /\ length sm = v crypto_bytes + UI64.v mlen}
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack (r:I32.t{r == 0l})
    (requires fun h -> live h sm /\ live h smlen /\ live h m /\ live h sk /\
                    disjoint R.state sm /\ disjoint R.state smlen /\ disjoint R.state m /\ disjoint R.state sk /\
                    disjoint sm smlen /\ disjoint sm m /\ disjoint sm sk /\
                    disjoint smlen m /\ disjoint smlen sk /\ 
                    disjoint m sk)
    (ensures fun h0 _ h1 -> modifies3 R.state sm smlen h0 h1)

let crypto_sign sm smlen m mlen sk =
    recall R.state;
    push_frame();
    let smlen_sizet = create (size 1) (size 0) in
    assert(disjoint R.state smlen_sizet);
    qtesla_sign smlen_sizet (uint64_to_uint32 mlen) m sm sk;
    let smlen_sizet = smlen_sizet.(size 0) in
    smlen.(size 0) <- uint32_to_uint64 smlen_sizet;
    pop_frame();
    0l

val crypto_sign_open:
    m : buffer uint8
  -> mlen : lbuffer UI64.t 1ul
  -> sm : buffer uint8
  -> smlen : UI64.t{length sm = v smlen /\ length m = UI64.v smlen - v crypto_bytes}
  -> pk : lbuffer uint8 crypto_publickeybytes
  -> Stack (r:I32.t{r == 0l \/ r == (-1l) \/ r == (-2l) \/ r == (-3l)})
    (requires fun h -> live h m /\ live h mlen /\ live h sm /\ live h pk /\
                    disjoint m mlen /\ disjoint m sm /\ disjoint m pk /\
                    disjoint mlen sm /\ disjoint mlen pk /\
                    disjoint sm pk)
    (ensures fun h0 _ h1 -> modifies2 m mlen h0 h1)

let crypto_sign_open m mlen sm smlen pk =
    push_frame();
    let smlen = Lib.RawIntTypes.size_from_UInt32 (uint64_to_uint32 smlen) in
    let mlen_sizet = create (size 1) (size 0) in
    let res = qtesla_verify (smlen -. crypto_bytes) mlen_sizet m smlen sm pk in
    let mlen_sizet = mlen_sizet.(size 0) in
    mlen.(size 0) <- uint32_to_uint64 mlen_sizet;
    pop_frame();
    res
