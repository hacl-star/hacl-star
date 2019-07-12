module Hacl.RSAPSS

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib
open Hacl.SHA256

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val rsa_pss_sign:
    pow2_i:size_t
  -> modBits:size_t{0 < v modBits}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits}
  -> dBits:size_t{0 < v dBits /\ v dBits <= v modBits}
  -> pLen:size_t
  -> qLen:size_t{v (blocks modBits 64ul) + v (blocks eBits 64ul) + v (blocks dBits 64ul) + v pLen + v qLen < max_size_t}
  -> skey:lbignum (blocks modBits 64ul +. blocks eBits 64ul +. blocks dBits 64ul +. pLen +. qLen)
  -> rBlind:uint64
  -> sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits 8ul) - v sLen - v hLen - 2 >= 0}
  -> salt:lbytes sLen
  -> msgLen:size_t
  -> msg:lbytes msgLen
  -> sgnt:lbytes (blocks modBits 8ul)
  -> Stack unit
    (requires fun h ->
      live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
      disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer sgnt) h0 h1)
let rsa_pss_sign pow2_i modBits eBits dBits pLen qLen skey rBlind sLen salt msgLen msg sgnt =
  Hacl.Impl.RSA.rsa_sign pow2_i modBits eBits dBits pLen qLen skey rBlind sLen salt msgLen msg sgnt

val rsa_pss_verify:
    pow2_i:size_t
  -> modBits:size_t{0 < v modBits}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ v (blocks modBits 64ul) + v (blocks eBits 64ul) < max_size_t}
  -> pkey:lbignum (blocks modBits 64ul +. blocks eBits 64ul)
  -> sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits 8ul) - v sLen - v hLen - 2 >= 0}
  -> sgnt:lbytes (blocks modBits 8ul)
  -> msgLen:size_t
  -> msg:lbytes msgLen
  -> Stack bool
    (requires fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1)
let rsa_pss_verify pow2_i modBits eBits pkey sLen sgnt msgLen msg =
  Hacl.Impl.RSA.rsa_verify pow2_i modBits eBits pkey sLen sgnt msgLen msg
