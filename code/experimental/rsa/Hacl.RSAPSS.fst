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
    #sLen:size_nat -> #msgLen:size_nat -> #nLen:size_nat ->
    pow2_i:size_t{6 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ nLen + 1 < 2 * v pow2_i} ->
    modBits:size_t{0 < v modBits /\ nLen = v (bits_to_bn modBits)} ->
    eBits:size_t{0 < v eBits /\ v eBits <= v modBits} ->
    dBits:size_t{0 < v dBits /\ v dBits <= v modBits} ->
    pLen:size_t -> qLen:size_t{nLen + v (bits_to_bn eBits) + v (bits_to_bn dBits) + v pLen + v qLen < max_size_t} ->
    skey:lbignum (nLen + v (bits_to_bn eBits) + v (bits_to_bn dBits) + v pLen + v qLen) ->
    rBlind:uint64 ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - sLen - v hLen - 3 >= 0} -> salt:lbytes sLen ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen ->
    sgnt:lbytes (v (blocks modBits (size 8))) -> Stack unit
    (requires (fun h -> live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
	              disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 sgnt h0 h1))

let rsa_pss_sign #sLen #msgLen #nLen pow2_i modBits eBits dBits pLen qLen skey rBlind ssLen salt mmsgLen msg sgnt =
    //push_frame();
    Hacl.Impl.RSA.rsa_sign #sLen #msgLen #nLen pow2_i modBits eBits dBits pLen qLen skey rBlind ssLen salt mmsgLen msg sgnt
    //pop_frame()

val rsa_pss_verify:
    #sLen:size_nat -> #msgLen:size_nat -> #nLen:size_nat ->
    pow2_i:size_t{6 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ nLen + 1 < 2 * v pow2_i} ->
    modBits:size_t{0 < v modBits /\ nLen = v (bits_to_bn modBits)} ->
    eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ nLen + v (bits_to_bn eBits) < max_size_t} ->
    pkey:lbignum (nLen + v (bits_to_bn eBits)) ->
    ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - sLen - v hLen - 3 >= 0} ->
    sgnt:lbytes (v (blocks modBits (size 8))) ->
    mmsgLen:size_t{v mmsgLen == msgLen /\ msgLen < pow2 61} -> msg:lbytes msgLen -> Stack bool
    (requires (fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))

let rsa_pss_verify #sLen #msgLen #nLen pow2_i modBits eBits pkey ssLen sgnt mmsgLen msg =
    //push_frame();
    let res = Hacl.Impl.RSA.rsa_verify #sLen #msgLen pow2_i modBits eBits pkey ssLen sgnt mmsgLen msg in
    //pop_frame();
    res
