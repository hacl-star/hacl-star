module Hacl.Impl.QTesla.Gauss

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
open Hacl.Impl.QTesla.Platform
open Hacl.Impl.QTesla.Constants
open Hacl.Impl.QTesla.Globals
open Hacl.Impl.QTesla.Pack
open Hacl.Impl.QTesla.Poly

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --admit_smt_queries true"

private let _RADIX = size params_radix
private let _RADIX32 = size params_radix32
private let _CDT_ROWS = params_cdt_rows
private let _CDT_COLS = params_cdt_cols
private let _CHUNK_SIZE = size 512

// Override infix operators to be correct for sdigit_t.
private unfold let op_Plus_Hat = sdigit_op_Plus_Hat
private unfold let op_Subtraction_Hat = sdigit_op_Subtraction_Hat
private unfold let op_Amp_Hat = sdigit_op_Amp_Hat
private unfold let op_Hat_Hat = sdigit_op_Hat_Hat
private unfold let op_Bar_Hat = sdigit_op_Bar_Hat
private unfold let op_Greater_Greater_Hat = sdigit_op_Greater_Greater_Hat
private unfold let op_Less_Hat = sdigit_op_Less_Hat
private unfold let lognot = sdigit_lognot

private let _DFIELD:sdigit_t = (digit_to_sdigit ((digit_lognot (to_digit 0)) `digit_shift_right` 1ul))

private val _PRODIFF:
    #n: size_t
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> k: size_t{k <^ n}
  -> Stack unit
    (requires fun h -> live h diff /\ live h a_u /\ live h a_v /\ 
                    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 diff a_u a_v h0 h1)
  
let _PRODIFF #n diff a_u a_v k =
    push_frame();
    diff.(size 0) <- (diff.(size 0) +^ (a_v.(k) &^ _DFIELD) -^ (a_u.(k) &^ _DFIELD)) >>^ (_RADIX -. size 1);
    pop_frame()

private val _PROSWAP:
    #n: size_t
  -> swap: lbuffer sdigit_t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> k: size_t{k <^ n}
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h a_u /\ live h a_v /\
                    disjoint swap diff /\ disjoint swap a_u /\ disjoint swap a_v /\
		    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff a_u h0 h1 /\ modifies1 a_v h0 h1)

let _PROSWAP #n swap diff a_u a_v k =
    push_frame();
    swap.(size 0) <- (a_u.(k) ^^ a_v.(k)) &^ diff.(size 0);
    a_u.(k) <- a_u.(k) ^^ swap.(size 0);
    a_v.(k) <- a_v.(k) ^^ swap.(size 0);
    pop_frame()

private val _PROSWAPG:
    swap: lbuffer I32.t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> g_u: lbuffer I32.t (size 1)
  -> g_v: lbuffer I32.t (size 1)
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h g_u /\ live h g_v /\
                    disjoint swap diff /\ disjoint swap g_u /\ disjoint swap g_v /\
		    disjoint diff g_u /\ disjoint diff g_v /\ disjoint g_u g_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff g_u h0 h1 /\ modifies1 g_v h0 h1)

let _PROSWAPG swap diff g_u g_v =
    push_frame();
    let diffVal = diff.(size 0) in
    swap.(size 0) <- I32.((g_u.(size 0) ^^ g_v.(size 0)) &^ (sdigit_to_int32 diffVal));
    g_u.(size 0) <- I32.(g_u.(size 0) ^^ swap.(size 0));
    g_v.(size 0) <- I32.(g_v.(size 0) ^^ swap.(size 0));
    pop_frame()

private val _MINMAX0:
    #n: size_t
  -> swap: lbuffer sdigit_t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h a_u /\ live h a_v /\
                    disjoint swap diff /\ disjoint swap a_u /\ disjoint swap a_v /\
		    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff a_u h0 h1 /\ modifies1 a_v h0 h1)

let _MINMAX0 #n swap diff a_u a_v =
    push_frame();
    _PRODIFF diff a_u a_v 0ul;
    _PROSWAP swap diff a_u a_v 0ul;
    pop_frame()
 
private val _MINMAX1:
    #n: size_t
  -> swap: lbuffer sdigit_t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h a_u /\ live h a_v /\
                    disjoint swap diff /\ disjoint swap a_u /\ disjoint swap a_v /\
		    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff a_u h0 h1 /\ modifies1 a_v h0 h1)

let _MINMAX1 #n swap diff a_u a_v =
    push_frame();
    if _CDT_COLS >. size 1
    then (
        _PRODIFF diff a_u a_v 1ul;
	_MINMAX0 swap diff a_u a_v;
	_PROSWAP swap diff a_u a_v 1ul
	 )
    else ( _MINMAX0 swap diff a_u a_v );
    pop_frame()

private val _MINMAX2:
    #n: size_t
  -> swap: lbuffer sdigit_t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h a_u /\ live h a_v /\
                    disjoint swap diff /\ disjoint swap a_u /\ disjoint swap a_v /\
		    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff a_u h0 h1 /\ modifies1 a_v h0 h1)

let _MINMAX2 #n swap diff a_u a_v =
    push_frame();
    if _CDT_COLS >. size 2
    then (
        _PRODIFF diff a_u a_v 2ul;
	_MINMAX1 swap diff a_u a_v;
	_PROSWAP swap diff a_u a_v 2ul
	 )
    else ( _MINMAX1 swap diff a_u a_v );
    pop_frame()

private val _MINMAX3:
    #n: size_t
  -> swap: lbuffer sdigit_t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h a_u /\ live h a_v /\
                    disjoint swap diff /\ disjoint swap a_u /\ disjoint swap a_v /\
		    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff a_u h0 h1 /\ modifies1 a_v h0 h1)

let _MINMAX3 #n swap diff a_u a_v =
    push_frame();
    if _CDT_COLS >. size 3
    then (
        _PRODIFF diff a_u a_v 3ul;
	_MINMAX2 swap diff a_u a_v;
	_PROSWAP swap diff a_u a_v 3ul
	 )
    else ( _MINMAX2 swap diff a_u a_v );
    pop_frame()

private val _MINMAX4:
    #n: size_t
  -> swap: lbuffer sdigit_t (size 1)
  -> diff: lbuffer sdigit_t (size 1)
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> Stack unit
    (requires fun h -> live h swap /\ live h diff /\ live h a_u /\ live h a_v /\
                    disjoint swap diff /\ disjoint swap a_u /\ disjoint swap a_v /\
		    disjoint diff a_u /\ disjoint diff a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies3 swap diff a_u h0 h1 /\ modifies1 a_v h0 h1)

let _MINMAX4 #n swap diff a_u a_v =
    push_frame();
    if _CDT_COLS >. size 4
    then (
        _PRODIFF diff a_u a_v 4ul;
	_MINMAX3 swap diff a_u a_v;
	_PROSWAP swap diff a_u a_v 4ul
	 )
    else ( _MINMAX3 swap diff a_u a_v );
    pop_frame()

// Reference implementation generates a compile-time error if _CDT_COLS is more than 5. We are just going
// to assume it is less than or equal to.
private val _MINIMAX:
    #n: size_t
  -> a_u: lbuffer sdigit_t n
  -> a_v: lbuffer sdigit_t n
  -> g_u: lbuffer I32.t (size 1)
  -> g_v: lbuffer I32.t (size 1)
  -> Stack unit
    (requires fun h -> live h a_u /\ live h a_v /\ live h g_u /\ live h g_v /\
                    disjoint a_u a_v /\ disjoint a_u g_u /\ disjoint a_u g_v /\
		    disjoint a_v g_u /\ disjoint a_v g_v /\ disjoint g_u g_v)
    (ensures fun h0 _ h1 -> modifies3 a_u a_v g_u h0 h1 /\ modifies1 g_v h0 h1)

let _MINIMAX #n a_u a_v g_u g_v =
    push_frame();
    assume(v _CDT_COLS <= 5);
    let diff:lbuffer sdigit_t (size 1) = create (size 1) (to_sdigit 0) in
    let swapa:lbuffer sdigit_t (size 1) = create (size 1) (to_sdigit 0) in
    let swapg:lbuffer I32.t (size 1) = create (size 1) 0l in
    _MINMAX4 swapa diff a_u a_v;
    _PROSWAPG swapg diff g_u g_v;
    pop_frame()

private val knuthMergeExchangeKG:
    n: size_t
  -> a: lbuffer sdigit_t (n *. _CDT_COLS)
  -> g: lbuffer I32.t n
  -> Stack unit
    (requires fun h -> live h a /\ live h g /\ disjoint a g)
    (ensures fun h0 _ h1 -> modifies2 a g h0 h1)

let knuthMergeExchangeKG n a g =
    push_frame();
    let t = create (size 1) (size 1) in
    while
    #(fun h -> live h t)
    #(fun _ h -> live h t)
    (fun _ -> t.(size 0) <. (n -. t.(size 0)))
    (fun _ -> t.(size 0) <- t.(size 0) +. t.(size 0));

    let pBuf = create (size 1) t.(size 0) in
    while
    #(fun h -> live h a /\ live h g /\ live h pBuf /\ live h t)
    #(fun _ h -> live h a /\ live h g /\ live h pBuf /\ live h t)
    (fun _ -> pBuf.(size 0) >. size 0)
    (fun _ ->
        push_frame();
	let p = pBuf.(size 0) in
        let ap = sub a (p *. _CDT_COLS) ((n -. p) *. _CDT_COLS) in
	let a_i = create (size 1) a in
	let ap_i = create (size 1) ap in
	let gp = sub g p _CDT_COLS in
	for (size 0) (n -. p)
	(fun h _ -> live h a /\ live h g /\ live h pBuf)
	(fun i -> if (i &. p) = size 0
	       then ( _MINIMAX a_i.(size 0) ap_i.(size 0) (sub g i (size 1)) (sub gp i (size 1)) )
	       else ();

               a_i.(size 0) <- sub a_i.(size 0) _CDT_COLS ((n -. i -. size 1) *. _CDT_COLS); 
	       ap_i.(size 0) <- sub ap_i.(size 0) _CDT_COLS ((n -. p -. i -. size 1) *. _CDT_COLS)
	);

        let qBuf = create (size 1) t.(size 0) in        
        while
	#(fun h -> live h a /\ live h g /\ live h pBuf /\ live h qBuf /\ live h t)
	#(fun _ h -> live h a /\ live h g /\ live h pBuf /\ live h qBuf /\ live h t)
	(fun _ -> qBuf.(size 0) >. p)
	(fun _ ->
	    push_frame();
	    let q = qBuf.(size 0) in
	    let ap_i = create (size 1) ap in
	    let aq_i = create (size 1) (sub a (q *. _CDT_COLS) ((n -. q) *. _CDT_COLS)) in
	    let gq = sub g q (n -. q) in
	    for (size 0) (n -. q)
	    (fun h _ -> live h a /\ live h g /\ live h pBuf /\ live h qBuf)
	    (fun i ->
	        if (i &. p) = size 0
		then ( _MINIMAX ap_i.(size 0) aq_i.(size 0) (sub gp i (size 1)) (sub gq i (size 1)) )
		else ();

                //ap_i.(size 0) <- sub ap ((i +. size 1) *. _CDT_COLS) ((n -. i -. size 1) *. _CDT_COLS);
		//aq_i.(size 0) <- sub a ((q +. i +. size 1) *. _CDT_COLS) ((n -. q -. i -. size 1) *. _CDT_COLS)
                ap_i.(size 0) <- sub ap_i.(size 0) _CDT_COLS ((n -. i -. size 1) *. _CDT_COLS);
		aq_i.(size 0) <- sub aq_i.(size 0) _CDT_COLS ((n -. q -. i -. size 1) *. _CDT_COLS)
	    );

            qBuf.(size 0) <- q >>. size 1;
	    pop_frame()
        );

        pBuf.(size 0) <- p >>. size 1;
	pop_frame()
    );

    pop_frame()

private val _MINMAXG:
    a_u: lbuffer I32.t (size 1)
  -> a_v: lbuffer I32.t (size 1)
  -> Stack unit
    (requires fun h -> live h a_u /\ live h a_v /\ disjoint a_u a_v)
    (ensures fun h0 _ h1 -> modifies2 a_u a_v h0 h1)

let _MINMAXG a_u a_v =
    push_frame();
    let diff = I32.(((a_v.(size 0) &^ 0x7FFFFFFFl) -^ (a_u.(size 0) &^ 0x7FFFFFFFl)) >>^ (_RADIX32 -. size 1)) in
    let swap = I32.((a_u.(size 0) ^^ a_v.(size 0)) &^ diff) in
    a_u.(size 0) <- I32.(a_u.(size 0) ^^ swap);
    a_v.(size 0) <- I32.(a_v.(size 0) ^^ swap);
    pop_frame()

private val knuthMergeExchangeG:
    n: size_t
  -> a: lbuffer I32.t n
  -> Stack unit
    (requires fun h -> live h a)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1)

let knuthMergeExchangeG n a =
    push_frame();
    if (n <=. size 1)
    then ()
    else (

    let t = create (size 1) (size 1) in
    while
    #(fun h -> live h t)
    #(fun _ h -> live h t)
    (fun _ -> t.(size 0) <. n -. t.(size 0))
    (fun _ -> t.(size 0) <- t.(size 0) +. t.(size 0));

    let pBuf = create (size 1) t.(size 0) in
    while
    #(fun h -> live h a /\ live h pBuf)
    #(fun _ h -> live h a /\ live h pBuf)
    (fun _ -> pBuf.(size 0) >. size 0)
    (fun _ ->
        push_frame();
	let p = pBuf.(size 0) in
        let ap = sub a p (n -. p) in
	for (size 0) (n -. p)
	(fun h _ -> live h a /\ live h pBuf)
	(fun i -> if (i &. p) = size 0
	       then ( _MINMAXG (sub a i (size 1)) (sub ap i (size 1)) )
	       else ()
	);

        let qBuf = create (size 1) t.(size 0) in
	while
	#(fun h -> live h a /\ live h qBuf)
	#(fun _ h -> live h a /\ live h qBuf)
	(fun _ -> qBuf.(size 0) >. p)
	(fun _ ->
	    let q = qBuf.(size 0) in
	    let aq = sub a q (n -. q) in
	    for (size 0) (n -. q)
	    (fun h _ -> live h a /\ live h qBuf)
	    (fun i -> if (i &. p) = size 0
	           then ( _MINMAXG (sub ap i (size 1)) (sub aq i (size 1)) )
		   else ()
            );

            qBuf.(size 0) <- q >>. size 1
        );

        pBuf.(size 0) <- p >>. size 1;
	pop_frame()
    )
    );
    pop_frame()

private val cSHAKE_sampk:
    sampk: lbuffer sdigit_t ((_CHUNK_SIZE +. _CDT_ROWS) *. _CDT_COLS)
  -> nonce: uint16
  -> seed: lbuffer uint8 crypto_randombytes
  -> Stack unit
    (requires fun h -> live h sampk /\ live h seed /\ disjoint sampk seed)
    (ensures fun h0 _ h1 -> modifies1 sampk h0 h1)

let cSHAKE_sampk sampk nonce seed =
    push_frame();
    let sampk_binary = create ((_CHUNK_SIZE +. _CDT_ROWS) *. _CDT_COLS *. (size sdigit_n /. size 8)) (u8 0) in
    params_cSHAKE crypto_randombytes seed nonce ((_CHUNK_SIZE +. _CDT_ROWS) *. _CDT_COLS *. (size sdigit_n /. size 8)) sampk_binary;

    // We aren't able to do reinterpreting casts in F* as is done in the reference implementation, so we incur some
    // extra copy cost here populating the sdigit_t buffer with the contents of the binary buffer recast as sdigit_t's.
    for (size 0) (_CHUNK_SIZE *. _CDT_COLS)
    (fun h _ -> live h sampk /\ live h sampk_binary)
    (fun i -> sampk.(i) <- let uintval = uint_from_bytes_le #digit_inttype #PUB (sub sampk_binary (i *. (size sdigit_n /. size 8)) (size sdigit_n /. size 8)) in digit_to_sdigit uintval);

    pop_frame()

private val kmxGauss:
    z: lbuffer elem _CHUNK_SIZE
  -> seed: lbuffer uint8 crypto_randombytes
  -> nonce: I32.t
  -> Stack unit
    (requires fun h -> live h z /\ live h seed /\ disjoint z seed)
    (ensures fun h0 _ h1 -> modifies1 z h0 h1)

let kmxGauss z seed nonce =
    push_frame();
    let cdt_v = createL params_cdt_v in
    let sampk = create ((_CHUNK_SIZE +. _CDT_ROWS) *. _CDT_COLS) (to_sdigit 0) in
    let (sampg:lbuffer I32.t (_CHUNK_SIZE +. _CDT_ROWS)) = create (_CHUNK_SIZE +. _CDT_ROWS) 0l in

    cSHAKE_sampk sampk nonce seed;
    update_sub sampk (_CHUNK_SIZE *. _CDT_COLS) (_CDT_ROWS *. _CDT_COLS) cdt_v;

    for (size 0) _CHUNK_SIZE
    (fun h _ -> live h sampg)
    (fun i -> sampg.(i) <- I32.((uint32_to_int32 i) <<^ 16ul));

    for (size 0) _CDT_ROWS
    (fun h _ -> live h sampg)
    (fun i -> sampg.(_CHUNK_SIZE +. i) <- I32.((uint32_to_int32 0xFFFF0000ul) ^^ (uint32_to_int32 i)));

    knuthMergeExchangeKG (_CHUNK_SIZE +. _CDT_ROWS) sampk sampg;

    let prev_inx = create (size 1) 0l in
    for (size 0) (_CHUNK_SIZE +. _CDT_ROWS)
    (fun h _ -> live h sampg /\ live h prev_inx /\ live h sampk)
    (fun i ->
        let curr_inx = I32.(sampg.(i) &^ 0xFFFFl) in
	prev_inx.(size 0) <- I32.(prev_inx.(size 0) ^^ ((curr_inx ^^ prev_inx.(size 0)) &^ ((prev_inx.(size 0) -^ curr_inx) >>^ (_RADIX32 -. size 1))));
	let neg = sampk.(i *. _CDT_COLS) >>^ (_RADIX -. size 1) in
	let neg = sdigit_to_int32 neg in
	sampg.(i) <- I32.(sampg.(i) |^ (((neg &^ ((-1l) *^ prev_inx.(size 0))) ^^ ((lognot neg) &^ prev_inx.(size 0))) &^ 0xFFFFl))
    );

    knuthMergeExchangeG (_CHUNK_SIZE +. _CDT_ROWS) sampg;

    for (size 0) _CHUNK_SIZE
    (fun h _ -> live h sampg /\ live h z)
    (fun i -> z.(i) <- 
        let result = I32.((sampg.(i) <<^ (_RADIX32 -. size 16)) >>^ (_RADIX32 -. size 16)) in
        int32_to_elem result
    );

    pop_frame()

val sample_gauss_poly:
    z: poly
  -> seed: lbuffer uint8 crypto_randombytes
  -> nonce: I32.t
  -> Stack unit
    (requires fun h -> live h z /\ live h seed /\ disjoint z seed)
    (ensures fun h0 _ h1 -> modifies1 z h0 h1) 

let sample_gauss_poly z seed nonce =
    push_frame();
    let dmsp = create (size 1) I32.(nonce <<^ 8ul) in
    // Reference code goes from 0 to param_n by steps of size _CHUNK_SIZE. To avoid having to use a while loop,
    // which we do for other for loops that use other operations as the increment (like right shifts),
    // we use the for loop, which only ever increments by one, and scale the iterator instead.
    for (size 0) (params_n /. _CHUNK_SIZE)
    (fun h _ -> live h z)
    (fun i ->
        let chunk = i *. _CHUNK_SIZE in
	kmxGauss (sub z chunk _CHUNK_SIZE) seed dmsp.(size 0);
	dmsp.(size 0) <- I32.(dmsp.(size 0) +^ 1l)
    );
    pop_frame()
    
