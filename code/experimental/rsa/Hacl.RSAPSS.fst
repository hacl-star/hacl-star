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
  pow2_i:size_t -> modBits:size_t{0 < v modBits} ->
  eBits:size_t{0 < v eBits /\ v eBits <= v modBits} -> dBits:size_t{0 < v dBits /\ v dBits <= v modBits} ->
  pLen:size_t -> qLen:size_t{v (blocks modBits (size 64)) + v (blocks eBits (size 64)) + v (blocks dBits (size 64)) + v pLen + v qLen < max_size_t} ->
  skey:lbignum (add #SIZE (add #SIZE (add #SIZE (add #SIZE (blocks modBits (size 64)) (blocks eBits (size 64))) (blocks dBits (size 64))) pLen) qLen) -> rBlind:uint64 ->
  sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - v sLen - v hLen - 2 >= 0} -> salt:lbytes sLen ->
  msgLen:size_t -> msg:lbytes msgLen -> sgnt:lbytes (blocks modBits (size 8)) -> Stack unit
  (requires (fun h -> live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
	            disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 sgnt h0 h1))

let rsa_pss_sign pow2_i modBits eBits dBits pLen qLen skey rBlind sLen salt msgLen msg sgnt =
  push_frame();
  Hacl.Impl.RSA.rsa_sign pow2_i modBits eBits dBits pLen qLen skey rBlind sLen salt msgLen msg sgnt;
  pop_frame()

val rsa_pss_verify:
  pow2_i:size_t -> modBits:size_t{0 < v modBits} ->
  eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ v (blocks modBits (size 64)) + v (blocks eBits (size 64)) < max_size_t} ->
  pkey:lbignum (add #SIZE (blocks modBits (size 64)) (blocks eBits (size 64))) ->
  sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - v sLen - v hLen - 2 >= 0} ->
  sgnt:lbytes (blocks modBits (size 8)) ->
  msgLen:size_t -> msg:lbytes msgLen -> Stack bool
  (requires (fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))
let rsa_pss_verify pow2_i modBits eBits pkey sLen sgnt msgLen msg =
  push_frame();
  let res = Hacl.Impl.RSA.rsa_verify pow2_i modBits eBits pkey sLen sgnt msgLen msg in
  pop_frame();
  res
