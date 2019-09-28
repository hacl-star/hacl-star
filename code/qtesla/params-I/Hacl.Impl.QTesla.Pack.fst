module Hacl.Impl.QTesla.Pack

open FStar.HyperStack
module HS = FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
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
module LL = Lib.Loops

open Hacl.Impl.QTesla.Params
open Hacl.Impl.QTesla.Globals
open Hacl.Impl.QTesla.ShiftArithmeticLeft
module SP = Spec.QTesla.Params

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

private inline_for_extraction noextract
val encode_sk_s:
    sk: lbuffer uint8 crypto_secretkeybytes
  -> s: poly
  -> j_in: size_t{v j_in + (v params_n `FStar.Int.op_Slash` 4) * 5 < v crypto_secretkeybytes}
  -> Stack size_t
    (requires fun h -> live h sk /\ live h s /\ disjoint sk s /\ is_poly_sk h s)
    (ensures fun h0 r h1 -> modifies1 sk h0 h1 /\ v r = v j_in + (v params_n `FStar.Int.op_Slash` 4) * 5)

let encode_sk_s sk s j_in =
    let h0 = ST.get () in
    assert_norm(v crypto_secretkeybytes > 0); 
    for 0ul (params_n /. size 4)
    (fun h _ -> live h sk /\ live h s /\ modifies1 sk h0 h /\ is_poly_sk h s)
    (fun k ->
        let i = k *. size 4 in
	let j = j_in +. k *. size 5 in
        let (/) = FStar.Int.op_Slash in

        assert(k <. params_n /. size 4);

        assert(v j_in + v k * 5 < v crypto_secretkeybytes); 

        let si0 = s.(i+.size 0) in    let si1 = s.(i+.size 1) in
	let si2 = s.(i+.size 2) in    let si3 = s.(i+.size 3) in
	
	sk.(j+.size 0) <- elem_to_uint8 si0;
	sk.(j+.size 1) <- elem_to_uint8 (((si0 >>>^ 8ul) &^ 0x03l) |^ (si1 <<<^ 2ul));
	sk.(j+.size 2) <- elem_to_uint8 (((si1 >>>^ 6ul) &^ 0x0Fl) |^ (si2 <<<^ 4ul));
	sk.(j+.size 3) <- elem_to_uint8 (((si2 >>>^ 4ul) &^ 0x3Fl) |^ (si3 <<<^ 6ul));
	sk.(j+.size 4) <- elem_to_uint8 (si3 >>>^ 2ul)
    );

    j_in +. (params_n /. size 4) *. size 5

let lemma_sk_when_k_one (h:HS.mem) (p:poly_k) : Lemma
    (requires is_poly_k_sk h p /\ v params_k == 1)
    (ensures is_poly_sk h p) = ()

val encode_sk:
    sk: lbuffer uint8 crypto_secretkeybytes
  -> s: poly
  -> e: poly_k
  -> seeds: lbuffer uint8 (size 2 *. crypto_seedbytes)
  -> Stack unit
    (requires fun h -> live h sk /\ live h s /\ live h e /\ live h seeds /\
                    disjoint sk s /\ disjoint sk e /\ disjoint sk seeds /\
                    disjoint s e /\ disjoint s seeds /\ disjoint e seeds /\
                    is_poly_sk h s /\ is_poly_k_sk h e)
    (ensures fun h0 _ h1 -> modifies1 sk h0 h1)

let encode_sk sk s e seeds =
    let hFrame = ST.get () in
    
    assert_norm(0 + (v params_n `FStar.Int.op_Slash` 4) * 5 < v crypto_secretkeybytes);
    let j = encode_sk_s sk s (size 0) in
    let h0 = ST.get () in
    assert(is_poly_k_equal hFrame h0 e);
    lemma_sk_when_k_one h0 e;
    assert(is_poly_sk h0 e);
    let _ = encode_sk_s sk e j in
    
    assert_norm(v (size 2 *. params_s_bits *. params_n /. size 8) + v (size 2 *. crypto_seedbytes) <= v crypto_secretkeybytes);

    update_sub #MUT #_ #_ sk (size 2 *. params_s_bits *. params_n /. size 8) (size 2 *. crypto_seedbytes) seeds

inline_for_extraction noextract
let encode_or_pack_sk = encode_sk

private inline_for_extraction noextract
val decode_sk_s:
    j_in : size_t{v j_in + 5 * (v params_n `FStar.Int.op_Slash` 4) <= v crypto_secretkeybytes}
  -> s : lbuffer I16.t params_n
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack size_t
    (requires fun h -> live h s /\ live h sk /\ disjoint s sk)
    (ensures fun h0 r h1 -> modifies1 s h0 h1 /\ is_s_sk h1 s /\ v r = v j_in + (v params_n `FStar.Int.op_Slash` 4) * 5)

let decode_sk_s j_in s sk =
    let h0 = ST.get () in
    for 0ul (params_n /. size 4)
    (fun h _ -> live h s /\ live h sk /\ modifies1 s h0 h)
    (fun k ->
        assert(k <. params_n /. size 4);
        let i = k *. size 4 in
	let j = j_in +. k *. size 5 in

        let skj0 = sk.(j+.size 0) in    [@inline_let] let skj0 = Lib.RawIntTypes.u8_to_UInt8 skj0 in    
        let skj1 = sk.(j+.size 1) in    [@inline_let] let skj1 = Lib.RawIntTypes.u8_to_UInt8 skj1 in
	let skj2 = sk.(j+.size 2) in    [@inline_let] let skj2 = Lib.RawIntTypes.u8_to_UInt8 skj2 in    
        let skj3 = sk.(j+.size 3) in    [@inline_let] let skj3 = Lib.RawIntTypes.u8_to_UInt8 skj3 in
	let skj4 = sk.(j+.size 4) in    [@inline_let] let skj4 = Lib.RawIntTypes.u8_to_UInt8 skj4 in

        [@inline_let] let (<<<^) = shift_arithmetic_left_i32 in
        
        s.(i+.size 0) <- I16.(uint8_to_int16 skj0               |^ int32_to_int16 I32.(((uint8_to_int32 skj1) <<<^ 30ul) >>>^ 22ul));
	s.(i+.size 1) <- I16.(uint8_to_int16 UI8.(skj1 >>^ 2ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj2) <<<^ 28ul) >>>^ 22ul));
	s.(i+.size 2) <- I16.(uint8_to_int16 UI8.(skj2 >>^ 4ul) |^ int32_to_int16 I32.(((uint8_to_int32 skj3) <<<^ 26ul) >>>^ 22ul));
        [@inline_let] let (<<<^) = shift_arithmetic_left_i16 in

	s.(i+.size 3) <- I16.(uint8_to_int16 UI8.(skj3 >>^ 6ul) |^ (int8_to_int16 (uint8_to_int8 skj4)) <<<^ 2ul)
    );

    let hReturn = ST.get () in
    // ASSUMPTION per Patrick: The input secret key is assumed to be trustworthy. The reference code does not actually
    // check that all coefficients are within the expected bounds, so we assume it here.
    assume(is_s_sk hReturn s);
    j_in +. (params_n /. size 4) *. size 5

val decode_sk:
    seeds : lbuffer uint8 (size 2 *. crypto_seedbytes)
  -> s : lbuffer I16.t params_n
  -> e : lbuffer I16.t params_n
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack unit
    (requires fun h -> live h seeds /\ live h s /\ live h e /\ live h sk /\
                    disjoint seeds s /\ disjoint seeds e /\ disjoint seeds sk /\
		    disjoint s e /\ disjoint s sk /\ disjoint e sk)
    (ensures fun h0 _ h1 -> modifies3 seeds s e h0 h1 /\ is_s_sk h1 s /\ is_e_sk h1 e)

let decode_sk seeds s e sk =
    let h0 = ST.get () in
    let j = decode_sk_s (size 0) s sk in
    let h1 = ST.get () in
    assert(modifies1 s h0 h1);
    let _ = decode_sk_s j e sk in
    let h2 = ST.get () in
    assert(modifies2 s e h0 h2);
    copy seeds (sub sk (size 2 *. params_s_bits *. params_n /. size 8) (size 2 *. crypto_seedbytes));  

    let h3 = ST.get () in
    assert(forall (i:nat{i < v params_n}) . bget h1 s i == bget h3 s i);
    assert(forall (i:nat{i < v params_n}) . bget h2 e i == bget h3 e i);
    assert(modifies3 s e seeds h0 h3)

// These four functions have the same implementation as III-size, so we share its code.
inline_for_extraction noextract
let encode_pk = Hacl.Impl.QTesla.Heuristic.Pack.encode_pk

inline_for_extraction noextract
let decode_pk = Hacl.Impl.QTesla.Heuristic.Pack.decode_pk

inline_for_extraction noextract
let encode_sig = Hacl.Impl.QTesla.Heuristic.Pack.encode_sig

inline_for_extraction noextract
let decode_sig = Hacl.Impl.QTesla.Heuristic.Pack.decode_sig
