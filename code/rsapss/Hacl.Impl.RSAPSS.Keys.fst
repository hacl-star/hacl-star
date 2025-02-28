module Hacl.Impl.RSAPSS.Keys

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module LSeq = Lib.Sequence

module LS = Hacl.Spec.RSAPSS
module BN = Hacl.Bignum
module BB = Hacl.Spec.Bignum.Base
module BE = Hacl.Bignum.Exponentiation


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val rsapss_check_pkey_len:
    #t:limb_t
  -> modBits:size_t
  -> eBits:size_t ->
  res:bool{res <==> LS.pkey_len_pre t (v modBits) (v eBits)}

let rsapss_check_pkey_len #t modBits eBits =
  if 1ul <. modBits && 0ul <. eBits then begin
    [@inline_let] let bits = size (bits t) in
    let nLen = blocks modBits bits in
    let eLen = blocks eBits bits in

    nLen <=. 0xfffffffful /. (2ul *! bits) && eLen <=. 0xfffffffful /. bits &&
    nLen +! nLen <=. 0xfffffffful -. eLen end
  else false


inline_for_extraction noextract
val rsapss_check_skey_len:
    #t:limb_t
  -> modBits:size_t
  -> eBits:size_t
  -> dBits:size_t ->
  res:bool{res <==> LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}

let rsapss_check_skey_len #t modBits eBits dBits =
  if rsapss_check_pkey_len #t modBits eBits && 0ul <. dBits then begin
    [@inline_let] let bits = size (bits t) in
    let nLen = blocks modBits bits in
    let eLen = blocks eBits bits in
    let dLen = blocks dBits bits in

    dLen <=. 0xfffffffful /. bits &&
    2ul *! nLen <=. 0xfffffffful -! eLen -! dLen end
  else false


inline_for_extraction noextract
let bn_check_num_bits_st (t:limb_t) =
    bs:size_t{0 < v bs /\ bits t * v (blocks bs (size (bits t))) <= max_size_t}
  -> b:lbignum t (blocks bs (size (bits t))) ->
  Stack (limb t)
  (requires fun h -> live h b)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.bn_check_num_bits (v bs) (as_seq h0 b))


inline_for_extraction noextract
val bn_check_num_bits: #t:limb_t -> bn_check_num_bits_st t
let bn_check_num_bits #t bs b =
  [@inline_let] let bits = size (bits t) in
  let bLen = blocks bs bits in
  if bs =. bits *! bLen then ones t SEC else BN.bn_lt_pow2_mask bLen b bs


inline_for_extraction noextract
let rsapss_check_modulus_st (t:limb_t) =
    modBits:size_t{0 < v modBits /\ bits t * v (blocks modBits (size (bits t))) <= max_size_t}
  -> n:lbignum t (blocks modBits (size (bits t))) ->
  Stack (limb t)
  (requires fun h -> live h n)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_check_modulus (v modBits) (as_seq h0 n))


inline_for_extraction noextract
val rsapss_check_modulus:
    #t:limb_t
  -> bn_check_num_bits:bn_check_num_bits_st t ->
  rsapss_check_modulus_st t

let rsapss_check_modulus #t bn_check_num_bits modBits n =
  let nLen = blocks modBits (size (bits t)) in
  let bits0 = BN.bn_is_odd nLen n in
  let m0 = uint #t 0 -. bits0 in
  let m1 = BN.bn_gt_pow2_mask nLen n (modBits -! 1ul) in
  let m2 = bn_check_num_bits modBits n in
  m0 &. (m1 &. m2)


inline_for_extraction noextract
let rsapss_check_exponent_st (t:limb_t) =
    eBits:size_t{0 < v eBits /\ bits t * v (blocks eBits (size (bits t))) <= max_size_t}
  -> e:lbignum t (blocks eBits (size (bits t))) ->
  Stack (limb t)
  (requires fun h -> live h e)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_check_exponent (v eBits) (as_seq h0 e))


inline_for_extraction noextract
val rsapss_check_exponent:
  #t:limb_t
  -> bn_check_num_bits:bn_check_num_bits_st t ->
  rsapss_check_exponent_st t

let rsapss_check_exponent #t bn_check_num_bits eBits e =
  let eLen = blocks eBits (size (bits t)) in
  let m0 = BN.bn_is_zero_mask eLen e in
  let m1 = bn_check_num_bits eBits e in
  (lognot m0) &. m1


inline_for_extraction noextract
class rsapss_checks (t:limb_t) = {
  check_num_bits: bn_check_num_bits_st t;
  check_modulus: rsapss_check_modulus_st t;
  check_exponent: rsapss_check_exponent_st t;
}

[@CInline]
let check_num_bits_u32 : bn_check_num_bits_st U32 =
  bn_check_num_bits
[@CInline]
let check_modulus_u32 : rsapss_check_modulus_st U32 =
  rsapss_check_modulus check_num_bits_u32
[@CInline]
let check_exponent_u32 : rsapss_check_exponent_st U32 =
  rsapss_check_exponent check_num_bits_u32


inline_for_extraction noextract
val mk_runtime_rsapss_checks_uint32: rsapss_checks U32
let mk_runtime_rsapss_checks_uint32 = {
  check_num_bits = check_num_bits_u32;
  check_modulus = check_modulus_u32;
  check_exponent = check_exponent_u32;
}

[@CInline]
let check_num_bits_u64 : bn_check_num_bits_st U64 =
  bn_check_num_bits
[@CInline]
let check_modulus_u64 : rsapss_check_modulus_st U64 =
  rsapss_check_modulus check_num_bits_u64
[@CInline]
let check_exponent_u64 : rsapss_check_exponent_st U64 =
  rsapss_check_exponent check_num_bits_u64


inline_for_extraction noextract
val mk_runtime_rsapss_checks_uint64: rsapss_checks U64
let mk_runtime_rsapss_checks_uint64 = {
  check_num_bits = check_num_bits_u64;
  check_modulus = check_modulus_u64;
  check_exponent = check_exponent_u64;
}

inline_for_extraction noextract
let mk_runtime_rsapss_checks (#t:limb_t) : rsapss_checks t =
  match t with
  | U32 -> mk_runtime_rsapss_checks_uint32
  | U64 -> mk_runtime_rsapss_checks_uint64


//pkey = [n; r2; e]
inline_for_extraction noextract
let rsapss_load_pkey_st (t:limb_t) (ke:BE.exp t) (modBits:size_t) =
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> pkey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t))) ->
  Stack bool
  (requires fun h ->
    blocks modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h nb /\ live h eb /\ live h pkey /\
    disjoint pkey nb /\ disjoint pkey eb)
  (ensures  fun h0 b h1 -> modifies (loc pkey) h0 h1 /\
   (b, as_seq h1 pkey) == LS.rsapss_load_pkey (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb))


inline_for_extraction noextract
val rsapss_load_pkey:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:size_t
  -> kc:rsapss_checks t ->
  rsapss_load_pkey_st t ke modBits

let rsapss_load_pkey #t ke modBits kc eBits nb eb pkey =
  let h0 = ST.get () in
  [@inline_let] let bits = size (bits t) in
  [@inline_let] let numb = size (numbytes t) in
  let nbLen = blocks modBits 8ul in
  let ebLen = blocks eBits 8ul in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  assert (v ((modBits -! 1ul) /. bits) < v nLen);

  LS.blocks_bits_lemma t (v modBits);
  assert (v (blocks nbLen numb) == v nLen);

  LS.blocks_bits_lemma t (v eBits);
  assert (v (blocks ebLen numb) == v eLen);

  let n  = sub pkey 0ul nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen +! nLen) eLen in

  BN.bn_from_bytes_be nbLen nb n;
  ke.BE.precompr2 (modBits -! 1ul) n r2;
  BN.bn_from_bytes_be ebLen eb e;
  let h1 = ST.get () in
  LSeq.lemma_concat3 (v nLen) (as_seq h1 n)
    (v nLen) (as_seq h1 r2) (v eLen) (as_seq h1 e) (as_seq h1 pkey);

  let m0 = kc.check_modulus modBits n in
  let m1 = kc.check_exponent eBits e in
  let m = m0 &. m1 in
  BB.unsafe_bool_of_limb #t m


#set-options "--z3rlimit 300"

//skey = [pkey; d]
inline_for_extraction noextract
let rsapss_load_skey_st (t:limb_t) (ke:BE.exp t) (modBits:size_t) =
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> db:lbuffer uint8 (blocks dBits 8ul)
  -> skey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t))) ->
  Stack bool
  (requires fun h ->
    blocks modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h nb /\ live h eb /\ live h db /\ live h skey /\
    disjoint skey nb /\ disjoint skey eb /\ disjoint skey db)
  (ensures  fun h0 b h1 -> modifies (loc skey) h0 h1 /\
    (b, as_seq h1 skey) == LS.rsapss_load_skey (v modBits) (v eBits) (v dBits)
      (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db))


inline_for_extraction noextract
val rsapss_load_skey:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:size_t
  -> kc:rsapss_checks t
  -> rsapss_load_pkey:rsapss_load_pkey_st t ke modBits ->
  rsapss_load_skey_st t ke modBits

let rsapss_load_skey #t ke modBits kc rsapss_load_pkey eBits dBits nb eb db skey =
  let h0 = ST.get () in
  [@inline_let] let bits = size (bits t) in
  [@inline_let] let numb = size (numbytes t) in
  let nbLen = blocks modBits 8ul in
  let ebLen = blocks eBits 8ul in
  let dbLen = blocks dBits 8ul in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let pkeyLen = nLen +! nLen +! eLen in
  let skeyLen = pkeyLen +! eLen in

  LS.blocks_bits_lemma t (v dBits);
  assert (v (blocks dbLen numb) == v dLen);

  let pkey = sub skey 0ul pkeyLen in
  let d = sub skey pkeyLen dLen in

  let b = rsapss_load_pkey eBits nb eb pkey in
  BN.bn_from_bytes_be dbLen db d;
  let h1 = ST.get () in
  LSeq.lemma_concat2 (v pkeyLen) (as_seq h1 pkey) (v dLen) (as_seq h1 d) (as_seq h1 skey);

  let m1 = kc.check_exponent dBits d in
  let b1 = b && BB.unsafe_bool_of_limb m1 in
  b1


inline_for_extraction noextract
let new_rsapss_load_pkey_st (t:limb_t) (ke:BE.exp t) (modBits:size_t) =
    r:HS.rid
  -> eBits:size_t
  -> nb:lbuffer uint8 (blocks0 modBits 8ul)
  -> eb:lbuffer uint8 (blocks0 eBits 8ul) ->
  ST (B.buffer (limb t))
  (requires fun h ->
    blocks0 modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h nb /\ live h eb /\ ST.is_eternal_region r)
  (ensures  fun h0 pkey h1 -> B.(modifies loc_none h0 h1) /\
    not (B.g_is_null pkey) ==> (
      LS.pkey_len_pre t (v modBits) (v eBits) /\
      B.(fresh_loc (loc_buffer pkey) h0 h1) /\
      B.freeable pkey /\
      B.(loc_includes (loc_region_only false r) (loc_buffer pkey)) /\
     (let bits = size (bits t) in
      let nLen = blocks modBits bits in
      let eLen = blocks eBits bits in
      let pkeyLen = nLen +! nLen +! eLen in
      B.len pkey == pkeyLen /\
     (let pkey = pkey <: lbignum t pkeyLen in

      LS.rsapss_load_pkey_post (v modBits) (v eBits)
	(as_seq h0 nb) (as_seq h0 eb) (as_seq h1 pkey)))))


inline_for_extraction noextract
val new_rsapss_load_pkey:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:size_t
  -> kc:rsapss_checks t ->
  new_rsapss_load_pkey_st t ke modBits

let new_rsapss_load_pkey #t ke modBits kc r eBits nb eb =
  [@inline_let] let bits = size (bits t) in

  if not (rsapss_check_pkey_len #t modBits eBits) then
   B.null
  else
    let h0 = ST.get () in
    let nLen = blocks modBits bits in
    let eLen = blocks eBits bits in
    let pkeyLen = nLen +! nLen +! eLen in
    let pkey = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) pkeyLen in
    if B.is_null pkey then
      pkey
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len pkey == pkeyLen);
      let pkey: Lib.Buffer.buffer (limb t) = pkey in
      assert (B.length pkey == FStar.UInt32.v pkeyLen);
      let pkey: lbignum t pkeyLen = pkey in
      let b = rsapss_load_pkey ke modBits kc eBits nb eb pkey in
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      LS.rsapss_load_pkey_lemma #t (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb);
      if b then pkey else begin
        B.free (pkey <: buffer (limb t));
        B.null end


inline_for_extraction noextract
let new_rsapss_load_skey_st (t:limb_t) (ke:BE.exp t) (modBits:size_t) =
    r:HS.rid
  -> eBits:size_t
  -> dBits:size_t
  -> nb:lbuffer uint8 (blocks0 modBits 8ul)
  -> eb:lbuffer uint8 (blocks0 eBits 8ul)
  -> db:lbuffer uint8 (blocks0 dBits 8ul) ->
  ST (B.buffer (limb t))
  (requires fun h ->
    blocks0 modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h nb /\ live h eb /\ live h db /\
    ST.is_eternal_region r)
  (ensures  fun h0 skey h1 -> B.(modifies loc_none h0 h1) /\
    not (B.g_is_null skey) ==> (
      LS.skey_len_pre t (v modBits) (v eBits) (v dBits) /\
      B.(fresh_loc (loc_buffer skey) h0 h1) /\
      B.freeable skey /\
      B.(loc_includes (loc_region_only false r) (loc_buffer skey)) /\
     (let bits = size (bits t) in
      let nLen = blocks modBits bits in
      let eLen = blocks eBits bits in
      let dLen = blocks dBits bits in
      let skeyLen = nLen +! nLen +! eLen +! dLen in

      B.len skey == skeyLen /\
     (let skey = skey <: lbignum t skeyLen in
      LS.rsapss_load_skey_post (v modBits) (v eBits) (v dBits)
	(as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db) (as_seq h1 skey)))))


#set-options "--z3rlimit 100"

inline_for_extraction noextract
val new_rsapss_load_skey:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:size_t
  -> kc:rsapss_checks t ->
  new_rsapss_load_skey_st t ke modBits

let new_rsapss_load_skey #t ke modBits kc r eBits dBits nb eb db =
  [@inline_let] let bits = size (bits t) in

  if not (rsapss_check_skey_len #t modBits eBits dBits) then
   B.null
  else begin
    assert (LS.skey_len_pre t (v modBits) (v eBits) (v dBits));
    let h0 = ST.get () in
    let nLen = blocks modBits bits in
    let eLen = blocks eBits bits in
    let dLen = blocks dBits bits in
    let skeyLen = nLen +! nLen +! eLen +! dLen in
    let skey = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t 0) skeyLen in
    if B.is_null skey then
      skey
    else
      let h1 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h1);
      assert (B.len skey == skeyLen);
      let skey: Lib.Buffer.buffer (limb t) = skey in
      assert (B.length skey == FStar.UInt32.v skeyLen);
      let skey: lbignum t skeyLen = skey in
      let b = rsapss_load_skey ke modBits kc (rsapss_load_pkey ke modBits kc) eBits dBits nb eb db skey in
      let h2 = ST.get () in
      B.(modifies_only_not_unused_in loc_none h0 h2);
      LS.rsapss_load_skey_lemma #t (v modBits) (v eBits) (v dBits)
	(as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db);
      if b then skey else begin
        B.free (skey <: buffer (limb t));
        B.null end
  end
