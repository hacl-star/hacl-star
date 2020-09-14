module Hacl.Impl.RSAKeys

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum
open Hacl.Bignum.Exponentiation

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module HS = FStar.HyperStack

module S = Spec.RSAPSS
module LS = Hacl.Spec.RSAPSS
module SB = Hacl.Spec.Bignum
module BM = Hacl.Bignum.Montgomery
module BN = Hacl.Bignum
module SM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


//pkey = [n; r2; e]
inline_for_extraction noextract
let rsapss_load_pkey_st =
    modBits:size_t
  -> eBits:size_t{LS.pkey_len_pre (v modBits) (v eBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> pkey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul) ->
  Stack unit
  (requires fun h -> live h nb /\ live h eb /\ live h pkey /\
    disjoint pkey nb /\ disjoint pkey eb)
  (ensures  fun h0 _ h1 -> modifies (loc pkey) h0 h1 /\
   (let nLen = blocks modBits 64ul in
    let eLen = blocks eBits 64ul in

    let n = gsub pkey 0ul nLen in
    let r2 = gsub pkey nLen nLen in
    let e = gsub pkey (nLen +! nLen) eLen in
    as_seq h1 n == SB.bn_from_bytes_be (v (blocks modBits 8ul)) (as_seq h0 nb) /\
    as_seq h1 r2 == SM.precomp_r2_mod_n (as_seq h1 n) /\
    as_seq h1 e == SB.bn_from_bytes_be (v (blocks eBits 8ul)) (as_seq h0 eb)))

inline_for_extraction noextract
val rsapss_load_pkey: rsapss_load_pkey_st
let rsapss_load_pkey modBits eBits nb eb pkey =
  let nbLen = blocks modBits 8ul in
  let ebLen = blocks eBits 8ul in

  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in

  LS.blocks_bits_lemma (v modBits);
  LS.blocks_bits_lemma1 (v modBits);
  assert (0 < v nbLen /\ 8 * v nbLen <= max_size_t);
  assert (v (blocks nbLen 8ul) == v nLen);

  LS.blocks_bits_lemma (v eBits);
  LS.blocks_bits_lemma1 (v eBits);
  assert (0 < v ebLen /\ 8 * v ebLen <= max_size_t);
  assert (v (blocks ebLen 8ul) == v eLen);

  let n  = sub pkey 0ul nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen +! nLen) eLen in

  bn_from_bytes_be nbLen nb n;
  BM.precomp_r2_mod_n #nLen #(BN.mk_runtime_bn nLen) n r2;
  bn_from_bytes_be ebLen eb e


#set-options "--z3rlimit 150"

//skey = [pkey; d]
inline_for_extraction noextract
let rsapss_load_skey_st =
    modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{LS.skey_len_pre (v modBits) (v eBits) (v dBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> db:lbuffer uint8 (blocks dBits 8ul)
  -> skey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul +! blocks dBits 64ul) ->
  Stack unit
  (requires fun h -> live h nb /\ live h eb /\ live h db /\ live h skey /\
    disjoint skey nb /\ disjoint skey eb /\ disjoint skey db)
  (ensures  fun h0 _ h1 -> modifies (loc skey) h0 h1 /\
   (let nLen = blocks modBits 64ul in
    let dLen = blocks dBits 64ul in
    let eLen = blocks eBits 64ul in

    let n = gsub skey 0ul nLen in
    let r2 = gsub skey nLen nLen in
    let e = gsub skey (nLen +! nLen) eLen in
    let d = gsub skey (nLen +! nLen +! eLen) dLen in
    as_seq h1 n == SB.bn_from_bytes_be (v (blocks modBits 8ul)) (as_seq h0 nb) /\
    as_seq h1 r2 == SM.precomp_r2_mod_n (as_seq h1 n) /\
    as_seq h1 e == SB.bn_from_bytes_be (v (blocks eBits 8ul)) (as_seq h0 eb) /\
    as_seq h1 d == SB.bn_from_bytes_be (v (blocks dBits 8ul)) (as_seq h0 db)))


inline_for_extraction noextract
val rsapss_load_skey: rsapss_load_skey_st
let rsapss_load_skey modBits eBits dBits nb eb db skey =
  let nbLen = blocks modBits 8ul in
  let ebLen = blocks eBits 8ul in
  let dbLen = blocks dBits 8ul in

  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let dLen = blocks dBits 64ul in

  let pkeyLen = nLen +! nLen +! eLen in
  let skeyLen = pkeyLen +! eLen in

  LS.blocks_bits_lemma (v dBits);
  LS.blocks_bits_lemma1 (v dBits);
  assert (0 < v dbLen /\ 8 * v dbLen <= max_size_t);
  assert (v (blocks dbLen 8ul) == v dLen);

  let pkey = sub skey 0ul pkeyLen in
  let d = sub skey pkeyLen dLen in

  rsapss_load_pkey modBits eBits nb eb pkey;
  bn_from_bytes_be dbLen db d


inline_for_extraction noextract
let new_rsapss_load_pkey_st =
    r:HS.rid
  -> modBits:size_t{0 < v modBits}
  -> eBits:size_t{0 < v eBits}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul) ->
  ST (B.buffer uint64)
  (requires fun h -> live h nb /\ live h eb /\
    ST.is_eternal_region r)
  (ensures  fun h0 pkey h1 -> B.(modifies loc_none h0 h1) /\
    not (B.g_is_null pkey) ==> (
      LS.pkey_len_pre (v modBits) (v eBits) /\
      B.(fresh_loc (loc_buffer pkey) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer pkey)) /\
     (let nLen = blocks modBits 64ul in
      let eLen = blocks eBits 64ul in
      let pkeyLen = nLen +! nLen +! eLen in

      B.len pkey == pkeyLen /\
     (let pkey = pkey <: lbignum pkeyLen in
      let n  = gsub pkey 0ul nLen in
      let r2 = gsub pkey nLen nLen in
      let e  = gsub pkey (nLen +! nLen) eLen in

      as_seq h1 n == SB.bn_from_bytes_be (v (blocks modBits 8ul)) (as_seq h0 nb) /\
      as_seq h1 r2 == SM.precomp_r2_mod_n (as_seq h1 n) /\
      as_seq h1 e == SB.bn_from_bytes_be (v (blocks eBits 8ul)) (as_seq h0 eb)))))


inline_for_extraction noextract
val new_rsapss_load_pkey: new_rsapss_load_pkey_st
let new_rsapss_load_pkey r modBits eBits nb eb =
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let pkeyLen = nLen +! nLen +! eLen in

  if not (1ul <. modBits && 0ul <. eBits &&
    nLen <=. 0xfffffffful /. 128ul && eLen <=. 0xfffffffful /. 64ul &&
    nLen +! nLen <=. 0xfffffffful -. eLen) then
   B.null
  else
    let h0 = ST.get () in
    let pkey = LowStar.Monotonic.Buffer.mmalloc_partial r (u64 0) pkeyLen in
    if B.is_null pkey then
      pkey
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len pkey == pkeyLen);
      let pkey: Lib.Buffer.buffer Lib.IntTypes.uint64 = pkey in
      assert (B.length pkey == FStar.UInt32.v pkeyLen);
      let pkey: lbignum pkeyLen = pkey in
      rsapss_load_pkey modBits eBits nb eb pkey;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      pkey


inline_for_extraction noextract
let new_rsapss_load_skey_st =
    r:HS.rid
  -> modBits:size_t{0 < v modBits}
  -> eBits:size_t{0 < v eBits}
  -> dBits:size_t{0 < v dBits}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> db:lbuffer uint8 (blocks dBits 8ul) ->
  ST (B.buffer uint64)
  (requires fun h -> live h nb /\ live h eb /\ live h db /\
    ST.is_eternal_region r)
  (ensures  fun h0 skey h1 -> B.(modifies loc_none h0 h1) /\
    not (B.g_is_null skey) ==> (
      LS.skey_len_pre (v modBits) (v eBits) (v dBits) /\
      B.(fresh_loc (loc_buffer skey) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer skey)) /\
     (let nLen = blocks modBits 64ul in
      let eLen = blocks eBits 64ul in
      let dLen = blocks dBits 64ul in
      let skeyLen = nLen +! nLen +! eLen +! dLen in

      B.len skey == skeyLen /\
     (let skey = skey <: lbignum skeyLen in
      let n  = gsub skey 0ul nLen in
      let r2 = gsub skey nLen nLen in
      let e  = gsub skey (nLen +! nLen) eLen in
      let d = gsub skey (nLen +! nLen +! eLen) dLen in

      as_seq h1 n == SB.bn_from_bytes_be (v (blocks modBits 8ul)) (as_seq h0 nb) /\
      as_seq h1 r2 == SM.precomp_r2_mod_n (as_seq h1 n) /\
      as_seq h1 e == SB.bn_from_bytes_be (v (blocks eBits 8ul)) (as_seq h0 eb) /\
      as_seq h1 d == SB.bn_from_bytes_be (v (blocks dBits 8ul)) (as_seq h0 db)))))


inline_for_extraction noextract
val new_rsapss_load_skey: new_rsapss_load_skey_st
let new_rsapss_load_skey r modBits eBits dBits nb eb db =
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let dLen = blocks dBits 64ul in
  let skeyLen = nLen +! nLen +! eLen +! dLen in

  if not (1ul <. modBits && 0ul <. eBits && 0ul <. dBits &&
    nLen <=. 0xfffffffful /. 128ul && eLen <=. 0xfffffffful /. 64ul && dLen <=. 0xfffffffful /. 64ul &&
    nLen +! nLen <=. 0xfffffffful -. eLen -. dLen) then
   B.null
  else
    let h0 = ST.get () in
    let skey = LowStar.Monotonic.Buffer.mmalloc_partial r (u64 0) skeyLen in
    if B.is_null skey then
      skey
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len skey == skeyLen);
      let skey: Lib.Buffer.buffer Lib.IntTypes.uint64 = skey in
      assert (B.length skey == FStar.UInt32.v skeyLen);
      let skey: lbignum skeyLen = skey in
      rsapss_load_skey modBits eBits dBits nb eb db skey;
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      skey
