module Hacl.Impl.RSAPSS

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST

module Hash = Spec.Agile.Hash
module SB = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base
module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery

module S = Spec.RSAPSS
module LS = Hacl.Spec.RSAPSS

open Hacl.Impl.RSAPSS.Padding
open Hacl.Impl.RSAPSS.MGF
open Hacl.Impl.RSAPSS.Keys

#reset-options "--z3rlimit 300 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let rsapss_sign_st1 (t:limb_t) =
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> sLen:size_t
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h ->
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\ disjoint sgnt skey /\
    disjoint salt msg /\

    LS.rsapss_sign_pre a (v modBits) (v eBits) (v dBits) (as_seq h skey)
      (v sLen) (as_seq h salt) (v msgLen) (as_seq h msg))
  (ensures  fun h0 eq_m h1 -> modifies (loc sgnt) h0 h1 /\
    (eq_m, as_seq h1 sgnt) == LS.rsapss_sign_ a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v sLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_sign_: #t:limb_t -> ke:BE.exp t -> rsapss_sign_st1 t
let rsapss_sign_ #t ke a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  push_frame ();
  let h_init = ST.get () in
  [@inline_let] let bits = size (bits t) in
  [@inline_let] let numb = size (numbytes t) in
  //let nLen = blocks modBits bits in
  let nLen = ke.BE.mont.BM.bn.BN.len in
  assume (v (blocks modBits bits) == v nLen);
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n  = sub skey 0ul nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen +! nLen) eLen in
  let d  = sub skey (nLen +! nLen +! eLen) dLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m  = create nLen (uint #t 0) in
  let m' = create nLen (uint #t 0) in
  let s  = create nLen (uint #t 0) in

  pss_encode a sLen salt msgLen msg emBits em;
  LS.blocks_bits_lemma t (v emBits);
  assert (v (blocks emLen numb) == v (blocks emBits bits));

  let h' = ST.get () in
  update_sub_f h' m 0ul (blocks emLen numb)
    (fun h -> SB.bn_from_bytes_be (v emLen) (as_seq h' em))
    (fun _ -> BN.bn_from_bytes_be emLen em (sub m 0ul (blocks emLen numb)));

  let _ = ke.BE.ct_mod_exp_precomp n m dBits d r2 s in
  let _ = ke.BE.mod_exp_precomp n s eBits e r2 m' in

  let eq_m = BN.bn_eq_mask nLen m m' in
  mapT nLen s (logand eq_m) s;

  LS.blocks_bits_lemma t (v modBits);
  assert (v (blocks k numb) == v nLen);
  BN.bn_to_bytes_be k s sgnt;

  pop_frame ();
  BB.unsafe_bool_of_limb eq_m


inline_for_extraction noextract
let rsapss_sign_st (t:limb_t) =
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> sLen:size_t
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h ->
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\ disjoint sgnt skey /\
    disjoint salt msg /\

    LS.rsapss_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey))
  (ensures  fun h0 b h1 -> modifies (loc sgnt) h0 h1 /\
    (b, as_seq h1 sgnt) == LS.rsapss_sign a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v sLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) (as_seq h0 sgnt))


inline_for_extraction noextract
val rsapss_sign: #t:limb_t -> ke:BE.exp t -> rsapss_sign_st t
let rsapss_sign #t ke a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  let hLen = hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  assert (max_size_t < Hash.max_input_length a);

  let b =
    sLen <=. 0xfffffffful -! hLen -! 8ul &&
    sLen +! hLen +! 2ul <=. blocks (modBits -! 1ul) 8ul in

  if b then
    rsapss_sign_ ke a modBits eBits dBits skey sLen salt msgLen msg sgnt
  else
    false



inline_for_extraction noextract
val bn_lt_pow2:
    #t:limb_t
  -> modBits:size_t{1 < v modBits}
  -> m:lbignum t (blocks modBits (size (bits t))) ->
  Stack bool
  (requires fun h -> live h m)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == LS.bn_lt_pow2 (v modBits) (as_seq h0 m))

let bn_lt_pow2 #t modBits m =
  if not ((modBits -! 1ul) %. 8ul =. 0ul) then true
  else begin
    let get_bit = BN.bn_get_ith_bit (blocks modBits (size (bits t))) m (modBits -! 1ul) in
    BB.unsafe_bool_of_limb0 get_bit end


inline_for_extraction noextract
let rsapss_verify_st1 (t:limb_t) =
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t)))
  -> sLen:size_t
  -> sgnt:lbuffer uint8 (blocks modBits 8ul)
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h sgnt /\ live h pkey /\
    disjoint msg sgnt /\

    LS.rsapss_verify_pre a (v modBits) (v eBits) (as_seq h pkey)
      (v sLen) (v msgLen) (as_seq h msg))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_verify_ a (v modBits) (v eBits) (as_seq h0 pkey)
      (v sLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_verify_: #t:limb_t -> ke:BE.exp t -> rsapss_verify_st1 t
let rsapss_verify_ #t ke a modBits eBits pkey sLen sgnt msgLen msg =
  push_frame ();
  let h_init = ST.get () in
  [@inline_let] let bits = size (bits t) in
  [@inline_let] let numb = size (numbytes t) in

  let nLen = blocks modBits bits in
  assume (v nLen == v ke.BE.mont.BM.bn.BN.len);
  let eLen = blocks eBits bits in

  let n  = sub pkey 0ul nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen +! nLen) eLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m = create nLen (uint #t 0) in
  let s = create nLen (uint #t 0) in
  LS.blocks_bits_lemma t (v modBits);
  assert (v (blocks k numb) == v nLen);
  BN.bn_from_bytes_be k sgnt s;


  let mask = BN.bn_lt_mask nLen s n in
  let res =
    if BB.unsafe_bool_of_limb mask then begin
      let _ = ke.BE.mod_exp_precomp n s eBits e r2 m in
      LS.blocks_bits_lemma t (v emBits);
      assert (v (blocks emLen numb) == v (blocks emBits bits));

      if bn_lt_pow2 modBits m then begin
	let m1 = sub m 0ul (blocks emLen numb) in
	BN.bn_to_bytes_be emLen m1 em;
	pss_verify a sLen msgLen msg emBits em end
      else false end
    else false in
  pop_frame ();
  res


inline_for_extraction noextract
let rsapss_verify_st (t:limb_t) =
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! blocks modBits (size (bits t)) +! blocks eBits (size (bits t)))
  -> sLen:size_t
  -> k:size_t
  -> sgnt:lbuffer uint8 k
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h sgnt /\ live h pkey /\
    disjoint msg sgnt /\ disjoint msg pkey /\ disjoint sgnt msg /\

    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_verify a (v modBits) (v eBits) (as_seq h0 pkey)
      (v sLen) (v k) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_verify: #t:limb_t -> ke:BE.exp t -> rsapss_verify_st t
let rsapss_verify #t ke a modBits eBits pkey sLen k sgnt msgLen msg =
  let hLen = hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  assert (max_size_t < Hash.max_input_length a);
  assert (v msgLen <= max_size_t);
  assert (v hLen + 8 < max_size_t);

  let b =
    sLen <=. 0xfffffffful -! hLen -! 8ul &&
    k =. blocks modBits 8ul in

  if b then
    rsapss_verify_ ke a modBits eBits pkey sLen sgnt msgLen msg
  else
    false


inline_for_extraction noextract
let rsapss_skey_sign_st (t:limb_t) =
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> db:lbuffer uint8 (blocks dBits 8ul)
  -> sLen:size_t
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h ->
    live h salt /\ live h msg /\ live h sgnt /\
    live h nb /\ live h eb /\ live h db /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\
    disjoint sgnt nb /\ disjoint sgnt eb /\ disjoint sgnt db /\
    disjoint salt msg)
  (ensures  fun h0 b h1 -> modifies (loc sgnt) h0 h1 /\
   (let sgnt_s = S.rsapss_skey_sign a (v modBits) (v eBits) (v dBits)
     (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db) (v sLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) in
    if b then Some? sgnt_s /\ as_seq h1 sgnt == Some?.v sgnt_s else None? sgnt_s))


inline_for_extraction noextract
val rsapss_skey_sign: #t:limb_t -> ke:BE.exp t -> rsapss_skey_sign_st t
let rsapss_skey_sign #t ke a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  [@inline_let] let bits = size (bits t) in
  let h0 = ST.get () in
  push_frame ();
  let skey = create (2ul *! blocks modBits bits +! blocks eBits bits +! blocks dBits bits) (uint #t 0) in
  let b = rsapss_load_skey #t modBits eBits dBits nb eb db skey in
  LS.rsapss_load_skey_lemma #t (v modBits) (v eBits) (v dBits) (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db);

  let res =
    if b then
      rsapss_sign ke a modBits eBits dBits skey sLen salt msgLen msg sgnt
    else
      false in
  pop_frame ();
  let h1 = ST.get () in
  assert ((res, as_seq h1 sgnt) == LS.rsapss_skey_sign #t a (v modBits) (v eBits) (v dBits)
      (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db) (v sLen) (as_seq h0 salt)
      (v msgLen) (as_seq h0 msg) (as_seq h0 sgnt));
  res


inline_for_extraction noextract
let rsapss_pkey_verify_st (t:limb_t) =
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> sLen:size_t
  -> k:size_t
  -> sgnt:lbuffer uint8 k
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h sgnt /\ live h nb /\ live h eb /\
    disjoint msg sgnt /\ disjoint nb eb /\ disjoint sgnt nb /\
    disjoint sgnt eb /\ disjoint msg nb /\ disjoint msg eb)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.rsapss_pkey_verify a (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb)
      (v sLen) (v k) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_pkey_verify: #t:limb_t -> ke:BE.exp t -> rsapss_pkey_verify_st t
let rsapss_pkey_verify #t ke a modBits eBits nb eb sLen k sgnt msgLen msg =
  push_frame ();
  [@inline_let] let bits = size (bits t) in
  let pkey = create (2ul *! blocks modBits bits +! blocks eBits bits) (uint #t 0) in
  let h0 = ST.get () in
  let b = rsapss_load_pkey modBits eBits nb eb pkey in
  LS.rsapss_load_pkey_lemma #t (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb);

  let res =
    if b then
      rsapss_verify ke a modBits eBits pkey sLen k sgnt msgLen msg
    else
      false in
  pop_frame ();
  let h1 = ST.get () in
  assert (res == LS.rsapss_pkey_verify #t a (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb)
    (v sLen) (v k) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg));
  res
