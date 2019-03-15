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
	
	sk.(j+.size 0) <- elem_to_uint8 si0;
	sk.(j+.size 1) <- elem_to_uint8 (((si0 >>^ 8ul) &^ 0x03l) |^ (si1 <<^ 2ul));
	sk.(j+.size 2) <- elem_to_uint8 (((si1 >>^ 6ul) &^ 0x0Fl) |^ (si2 <<^ 4ul));
	sk.(j+.size 3) <- elem_to_uint8 (((si2 >>^ 4ul) &^ 0x3Fl) |^ (si3 <<^ 6ul));
	sk.(j+.size 4) <- elem_to_uint8 (si3 >>^ 2ul);

        jBuf.(size 0) <- j +. size 5;
	iBuf.(size 0) <- i +. size 4
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
	
	sk.(j+.size 0) <- elem_to_uint8 ei0;
	sk.(j+.size 1) <- elem_to_uint8 (((ei0 >>^ 8ul) &^ 0x03l) |^ (ei1 <<^ 2ul));
	sk.(j+.size 2) <- elem_to_uint8 (((ei1 >>^ 6ul) &^ 0x0Fl) |^ (ei2 <<^ 4ul));
	sk.(j+.size 3) <- elem_to_uint8 (((ei2 >>^ 4ul) &^ 0x3Fl) |^ (ei3 <<^ 6ul));
	sk.(j+.size 4) <- elem_to_uint8 (ei3 >>^ 2ul);

        jBuf.(size 0) <- j +. size 5;
	iBuf.(size 0) <- i +. size 4
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
	let skj4 = sk.(j+.size 4) in

        s.(i+.size 0) <- I16.(uint8_to_int16 skj0               |^ int32_to_int16 I32.(((uint8_to_int32 skj1) <<^ 30ul) >>^ 22ul));
	s.(i+.size 1) <- I16.(uint8_to_int16 UI8.(skj1 >>^ 2ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj2) <<^ 28ul) >>^ 22ul));
	s.(i+.size 2) <- I16.(uint8_to_int16 UI8.(skj2 >>^ 4ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj3) <<^ 26ul) >>^ 22ul));
	s.(i+.size 3) <- I16.(uint8_to_int16 UI8.(skj3 >>^ 6ul) |^ (int8_to_int16 (uint8_to_int8 skj4)) <<^ 2ul);

        jBuf.(size 0) <- j +. size 5;
	iBuf.(size 0) <- i +. size 4
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
	let skj4 = sk.(j+.size 4) in

        e.(i+.size 0) <- I16.(uint8_to_int16 skj0               |^ int32_to_int16 I32.(((uint8_to_int32 skj1) <<^ 30ul) >>^ 22ul));
	e.(i+.size 1) <- I16.(uint8_to_int16 UI8.(skj1 >>^ 2ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj2) <<^ 28ul) >>^ 22ul));
	e.(i+.size 2) <- I16.(uint8_to_int16 UI8.(skj2 >>^ 4ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj3) <<^ 26ul) >>^ 22ul));
	e.(i+.size 3) <- I16.(uint8_to_int16 UI8.(skj3 >>^ 6ul) |^ (int8_to_int16 (uint8_to_int8 skj4)) <<^ 2ul);

        jBuf.(size 0) <- j +. size 5;
	iBuf.(size 0) <- i +. size 4
    );

    copy seeds (sub sk (size 2 *. params_s_bits *. params_n /. size 8) (size 2 *. crypto_seedbytes));

    pop_frame()

// These four functions have the same implementation as III-size, so we share its code.
inline_for_extraction noextract
let encode_pk = Hacl.Impl.QTesla.Heuristic.Pack.encode_pk

inline_for_extraction noextract
let decode_pk = Hacl.Impl.QTesla.Heuristic.Pack.decode_pk

inline_for_extraction noextract
let encode_sig = Hacl.Impl.QTesla.Heuristic.Pack.encode_sig

inline_for_extraction noextract
let decode_sig = Hacl.Impl.QTesla.Heuristic.Pack.decode_sig
