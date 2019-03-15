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

    for 0ul params_n
    (fun h _ -> live h sk /\ live h s)
    (fun i -> let si = s.(i) in sk.(i) <- elem_to_uint8 si);

    for 0ul params_n
    (fun h _ -> live h sk /\ live h e)
    (fun i -> let ei = e.(i) in sk.(params_n +. i) <- elem_to_uint8 ei);

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

    for 0ul params_n
    (fun h _ -> live h sk /\ live h s)
    (fun i -> let ski = sk.(i) in s.(i) <- int8_to_int16 (uint8_to_int8 ski));

    for 0ul params_n
    (fun h _ -> live h sk /\ live h e)
    (fun i -> let ski = sk.(params_n +. i) in e.(i) <- int8_to_int16 (uint8_to_int8 ski));

    copy seeds (sub sk (size 2 *. params_s_bits *. params_n /. size 8) (size 2 *. crypto_seedbytes));

    pop_frame()

// These four functions have the same implementation as I, so we share its code.
inline_for_extraction noextract
let encode_pk = Hacl.Impl.QTesla.Heuristic.Pack.encode_pk

inline_for_extraction noextract
let decode_pk = Hacl.Impl.QTesla.Heuristic.Pack.decode_pk

inline_for_extraction noextract
let encode_sig = Hacl.Impl.QTesla.Heuristic.Pack.encode_sig

inline_for_extraction noextract
let decode_sig = Hacl.Impl.QTesla.Heuristic.Pack.decode_sig
