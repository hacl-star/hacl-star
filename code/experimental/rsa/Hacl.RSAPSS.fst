module Hacl.RSAPSS

open FStar.HyperStack.All
open FStar.Mul
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib
open Hacl.Impl.MGF

module Buffer = Spec.Lib.IntBuf

val rsa_pss_sign:
    #sLen:size_nat -> #msgLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    modBits:size_t{0 < v modBits /\ v modBits + 3 < max_size_t} ->
    eBits:size_t{0 < v eBits /\ v eBits <= v modBits} ->
    dBits:size_t{0 < v dBits /\ v dBits <= v modBits /\
		 v (bits_to_bn modBits) + v (bits_to_bn eBits) + v (bits_to_bn dBits) < max_size_t} ->
    skey:lbignum (v (bits_to_bn modBits) + v (bits_to_bn eBits) + v (bits_to_bn dBits)) ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - sLen - v hLen - 3 >= 0 } ->
    salt:lbytes sLen ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen ->
    sgnt:lbytes (v (blocks modBits (size 8))) -> Stack unit
    (requires (fun h -> live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
	              disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 sgnt h0 h1))

let rsa_pss_sign #sLen #msgLen pow2_i iLen modBits eBits dBits skey ssLen salt mmsgLen msg sgnt = 
    Hacl.Impl.RSA.rsa_sign #sLen #msgLen pow2_i iLen modBits eBits dBits skey ssLen salt mmsgLen msg sgnt

val rsa_pss_verify:
    #sLen:size_nat -> #msgLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    modBits:size_t{0 < v modBits /\ v modBits + 3 < max_size_t} ->
    eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\
		 v (bits_to_bn modBits) + v (bits_to_bn eBits) < max_size_t} ->
    pkey:lbignum (v (bits_to_bn modBits) + v (bits_to_bn eBits)) ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t} ->
    sgnt:lbytes (v (blocks modBits (size 8))) ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen -> Stack bool
    (requires (fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))

let rsa_pss_verify #sLen #msgLen pow2_i iLen modBits eBits pkey ssLen sgnt mmsgLen msg = 
    Hacl.Impl.RSA.rsa_verify #sLen #msgLen pow2_i iLen modBits eBits pkey ssLen sgnt mmsgLen msg
