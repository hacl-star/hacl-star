module Hacl.RSAPSS

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Impl.MGF

module ST = FStar.HyperStack.ST
module S = Spec.RSAPSS


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val rsapss_sign:
     modBits:size_t{1 < v modBits /\ 128 * (v (blocks modBits 64ul) + 1) <= max_size_t}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits}
  -> dBits:size_t{0 < v dBits /\ v dBits <= v modBits /\ v (blocks modBits 64ul) + v (blocks eBits 64ul) + v (blocks dBits 64ul) <= max_size_t}
  -> skey:lbignum (blocks modBits 64ul +! blocks eBits 64ul +! blocks dBits 64ul)
  -> sLen:size_t{v sLen + v hLen + 8 <= max_size_t /\ v sLen + v hLen + 8 < S.max_input /\ v sLen + v hLen + 2 <= v (blocks (modBits -! 1ul) 8ul)}
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt /\ disjoint sgnt skey /\
   (let nLen = blocks modBits 64ul in
    bn_v h (gsub skey 0ul nLen) > 0))
  (ensures  fun h0 _ h1 -> modifies (loc sgnt) h0 h1)

let rsapss_sign modBits eBits dBits skey sLen salt msgLen msg sgnt =
  Hacl.Impl.RSAPSS.rsapss_sign modBits eBits dBits skey sLen salt msgLen msg sgnt


val rsapss_verify:
    modBits:size_t{1 < v modBits /\ 128 * (v (blocks modBits 64ul) + 1) <= max_size_t}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ v (blocks modBits 64ul) + v (blocks eBits 64ul) <= max_size_t}
  -> pkey:lbignum (blocks modBits 64ul +! blocks eBits 64ul)
  -> sLen:size_t{v sLen + v hLen + 8 <= max_size_t /\ v sLen + v hLen + 8 < S.max_input}
  -> sgnt:lbuffer uint8 (blocks modBits 8ul)
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt /\
   (let nLen = blocks modBits 64ul in
    bn_v h (gsub pkey 0ul nLen) > 0))
  (ensures  fun h0 r h1 -> modifies0 h0 h1)

let rsapss_verify modBits eBits pkey sLen sgnt msgLen msg =
  Hacl.Impl.RSAPSS.rsapss_verify modBits eBits pkey sLen sgnt msgLen msg
