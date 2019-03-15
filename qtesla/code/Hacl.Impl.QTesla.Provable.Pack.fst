module Hacl.Impl.QTesla.Provable.Pack

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

val pack_sk:
    sk: lbuffer uint8 crypto_secretkeybytes
  -> s: poly
  -> e: poly_k
  -> seeds: lbuffer uint8 (2 *. crypto_seedbytes)
  -> Stack unit
    (requires fun h -> live h sk /\ live h s /\ live h e /\ live h seeds /\
                    disjoint sk s /\ disjoint sk e /\ disjoint sk seeds /\
                    disjoint s e /\ disjoint s seeds /\ disjoint e seeds)
    (ensures fun h0 _ h1 -> modifies1 sk h0 h1)

let pack_sk sk s e seeds =
    push_frame();

    for 0ul params_n
    (fun h _ -> live h sk /\ live h s)
    (fun i -> let si = s.(i) in sk.(i) <- elem_to_uint8 si);

    let sk = sub sk params_n (crypto_secretkeybytes -. params_n) in
    for 0ul params_k
    (fun h _ -> live h sk /\ live h e)
    (fun k -> for 0ul params_n
           (fun h0 _ -> live h0 sk /\ live h0 e)
	   (fun i -> let eVal = e.(k *. params_n +. i) in sk.(k *. params_n +. i) <- elem_to_uint8 eVal )
    );

    update_sub #MUT #_ #_ sk (params_k *. params_n) (size 2 *. crypto_seedbytes) seeds;

    pop_frame()

inline_for_extraction noextract
let encode_or_pack_sk = pack_sk

val decode_sk:
    seeds : lbuffer uint8 (size 2 *. crypto_seedbytes)
  -> s : lbuffer sparse_elem params_n
  -> e : lbuffer sparse_elem (params_n *. params_k)
  -> sk : lbuffer uint8 crypto_secretkeybytes
  -> Stack unit
    (requires fun h -> live h seeds /\ live h s /\ live h e /\ live h sk /\
                    disjoint seeds s /\ disjoint seeds e /\ disjoint seeds sk /\
		    disjoint s e /\ disjoint s sk /\ disjoint e sk)
    (ensures fun h0 _ h1 -> modifies (loc seeds |+| loc s |+| loc e) h0 h1)

let decode_sk seeds s e sk =
    push_frame();

    for 0ul params_n
    (fun h _ -> live h sk /\ live h s)
    (fun i -> let ski = sk.(i) in s.(i) <- uint8_to_int8 ski);

    for 0ul params_k
    (fun h _ -> live h sk /\ live h e)
    (fun k ->
        for 0ul params_n
	(fun h _ -> live h sk /\ live h e)
	(fun i -> let skVal = sk.(params_n *. (k +. size 1) +. i) in e.(params_n *. k +. i) <- uint8_to_int8 skVal)
    );

    copy seeds (sub sk (params_n +. params_k *. params_n) (size 2 *. crypto_seedbytes));

    pop_frame()

