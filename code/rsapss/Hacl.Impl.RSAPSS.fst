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
module SD = Hacl.Spec.Bignum.Definitions
module SM = Hacl.Spec.Bignum.Montgomery
module SE = Hacl.Spec.Bignum.Exponentiation

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery

module S = Spec.RSAPSS
module LS = Hacl.Spec.RSAPSS
module LSeq = Lib.Sequence

module RP = Hacl.Impl.RSAPSS.Padding
module RM = Hacl.Impl.RSAPSS.MGF
module RK = Hacl.Impl.RSAPSS.Keys

#reset-options "--z3rlimit 150 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let modBits_t (t:limb_t) = modBits:size_t{1 < v modBits /\ 2 * bits t * SD.blocks (v modBits) (bits t) <= max_size_t}


inline_for_extraction noextract
let rsapss_sign_bn_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> m:lbignum t len
  -> m':lbignum t len
  -> s:lbignum t len ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h skey /\ live h m /\ live h s /\ live h m' /\
    disjoint s m /\ disjoint s skey /\ disjoint m skey /\
    disjoint m m' /\ disjoint m' s /\ disjoint m' skey /\
    LS.rsapss_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey) /\
    bn_v h m < bn_v h (gsub skey 0ul len))
  (ensures  fun h0 r h1 -> modifies (loc s |+| loc m') h0 h1 /\
    (r, as_seq h1 s) == LS.rsapss_sign_bn (v modBits) (v eBits) (v dBits) (as_seq h0 skey) (as_seq h0 m))


inline_for_extraction noextract
val rsapss_sign_bn: #t:limb_t -> ke:BE.exp t -> modBits:modBits_t t -> rsapss_sign_bn_st t ke modBits
let rsapss_sign_bn #t ke modBits eBits dBits skey m m' s =
  [@inline_let] let bits : size_pos = bits t in
  let nLen = blocks modBits (size bits) in
  let eLen = blocks eBits (size bits) in
  let dLen = blocks dBits (size bits) in

  let n  = sub skey 0ul nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen +! nLen) eLen in
  let d  = sub skey (nLen +! nLen +! eLen) dLen in

  Math.Lemmas.pow2_le_compat (bits * v nLen) (v modBits);
  let h0 = ST.get () in
  SM.bn_precomp_r2_mod_n_lemma (v modBits - 1) (as_seq h0 n);
  BE.mk_bn_mod_exp_precompr2 nLen ke.BE.exp_ct_precomp n r2 m dBits d s;
  BE.mk_bn_mod_exp_precompr2 nLen ke.BE.exp_vt_precomp n r2 s eBits e m';
  let h1 = ST.get () in
  SD.bn_eval_inj (v nLen) (as_seq h1 s)
    (SE.bn_mod_exp_consttime_precompr2 (v nLen) (as_seq h0 n) (as_seq h0 r2)
    (as_seq h0 m) (v dBits) (as_seq h0 d));
  SD.bn_eval_inj (v nLen) (as_seq h1 m')
    (SE.bn_mod_exp_vartime_precompr2 (v nLen) (as_seq h0 n) (as_seq h0 r2)
    (as_seq h1 s) (v eBits) (as_seq h0 e));
  let eq_m = BN.bn_eq_mask nLen m m' in
  mapT nLen s (logand eq_m) s;
  BB.unsafe_bool_of_limb eq_m


inline_for_extraction noextract
let rsapss_sign_msg_to_bn_st (t:limb_t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
    saltLen:size_t
  -> salt:lbuffer uint8 saltLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> m:lbignum t len ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h m /\
    disjoint salt msg /\ disjoint m msg /\ disjoint m salt /\
    as_seq h m == LSeq.create (v len) (uint #t 0) /\
    LS.rsapss_sign_pre a (v modBits) (v saltLen) (as_seq h salt) (v msgLen) (as_seq h msg))
  (ensures  fun h0 _ h1 -> modifies (loc m) h0 h1 /\
    as_seq h1 m == LS.rsapss_sign_msg_to_bn a (v modBits) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_sign_msg_to_bn:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_sign_msg_to_bn_st t a modBits

let rsapss_sign_msg_to_bn #t a modBits saltLen salt msgLen msg m =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in

  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in
  [@inline_let] let mLen = blocks emLen (size numb) in

  let em = create emLen (u8 0) in
  RP.pss_encode a saltLen salt msgLen msg emBits em;
  LS.blocks_bits_lemma t (v emBits);
  LS.blocks_numb_lemma t (v emBits);
  assert (SD.blocks (v emBits) bits = v mLen);
  assert (numb * v mLen <= max_size_t);
  assert (v mLen <= v nLen);

  let h' = ST.get () in
  update_sub_f h' m 0ul mLen
    (fun h -> SB.bn_from_bytes_be (v emLen) (as_seq h' em))
    (fun _ -> BN.bn_from_bytes_be emLen em (sub m 0ul mLen));
  pop_frame ()


inline_for_extraction noextract
let rsapss_sign_compute_sgnt_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> m:lbignum t len
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h sgnt /\ live h skey /\ live h m /\
    disjoint sgnt skey /\ disjoint m sgnt /\ disjoint m skey /\
    LS.rsapss_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey) /\
    bn_v h m < bn_v h (gsub skey 0ul len))
  (ensures  fun h0 eq_m h1 -> modifies (loc sgnt) h0 h1 /\
    (eq_m, as_seq h1 sgnt) == LS.rsapss_sign_compute_sgnt (v modBits) (v eBits) (v dBits) (as_seq h0 skey) (as_seq h0 m))


inline_for_extraction noextract
val rsapss_sign_compute_sgnt:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:modBits_t t ->
  rsapss_sign_compute_sgnt_st t ke modBits

let rsapss_sign_compute_sgnt #t ke modBits eBits dBits skey m sgnt =
  push_frame ();
  let h_init = ST.get () in
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in

  let k = blocks modBits 8ul in
  let s = create nLen (uint #t 0) in
  let m' = create nLen (uint #t 0) in
  let eq_b = rsapss_sign_bn ke modBits eBits dBits skey m m' s in
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v k) numb == v nLen);
  assert (numb * v nLen <= max_size_t);
  BN.bn_to_bytes_be k s sgnt;
  pop_frame ();
  eq_b


inline_for_extraction noextract
let rsapss_sign_st1 (t:limb_t) (ke:BE.exp t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> saltLen:size_t
  -> salt:lbuffer uint8 saltLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\ disjoint sgnt skey /\
    disjoint salt msg /\

    LS.rsapss_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey) /\
    LS.rsapss_sign_pre a (v modBits) (v saltLen) (as_seq h salt) (v msgLen) (as_seq h msg))
  (ensures  fun h0 eq_m h1 -> modifies (loc sgnt) h0 h1 /\
    (eq_m, as_seq h1 sgnt) == LS.rsapss_sign_ a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_sign_:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_sign_st1 t ke a modBits

let rsapss_sign_ #t ke a modBits eBits dBits skey saltLen salt msgLen msg sgnt =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  let nLen = blocks modBits (size bits) in
  let m = create nLen (uint #t 0) in
  rsapss_sign_msg_to_bn a modBits saltLen salt msgLen msg m;
  let eq_b = rsapss_sign_compute_sgnt ke modBits eBits dBits skey m sgnt in
  pop_frame ();
  eq_b


inline_for_extraction noextract
let rsapss_sign_st (t:limb_t) (ke:BE.exp t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:modBits_t t) =
    let len = blocks modBits (size (bits t)) in
     eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> saltLen:size_t
  -> salt:lbuffer uint8 saltLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\ disjoint sgnt skey /\
    disjoint salt msg /\

    LS.rsapss_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey))
  (ensures  fun h0 b h1 -> modifies (loc sgnt) h0 h1 /\
    (b, as_seq h1 sgnt) == LS.rsapss_sign a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) (as_seq h0 sgnt))


inline_for_extraction noextract
val rsapss_sign:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_sign_st t ke a modBits

let rsapss_sign #t ke a modBits eBits dBits skey saltLen salt msgLen msg sgnt =
  let hLen = RM.hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  //assert (max_size_t < Hash.max_input_length a);

  let b =
    saltLen <=. 0xfffffffful -! hLen -! 8ul &&
    saltLen +! hLen +! 2ul <=. blocks (modBits -! 1ul) 8ul in

  if b then
    rsapss_sign_ ke a modBits eBits dBits skey saltLen salt msgLen msg sgnt
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
let rsapss_verify_bn_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> m_def:lbignum t len
  -> s:lbignum t len ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h pkey /\ live h m_def /\ live h s /\
    disjoint m_def pkey /\ disjoint m_def s /\ disjoint s pkey /\
    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies (loc m_def) h0 h1 /\
    (r, as_seq h1 m_def) == LS.rsapss_verify_bn (v modBits) (v eBits) (as_seq h0 pkey) (as_seq h0 m_def) (as_seq h0 s))


inline_for_extraction noextract
val rsapss_verify_bn: #t:limb_t -> ke:BE.exp t -> modBits:modBits_t t -> rsapss_verify_bn_st t ke modBits
let rsapss_verify_bn #t ke modBits eBits pkey m_def s =
  [@inline_let] let bits = size (bits t) in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0ul nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen +! nLen) eLen in

  let mask = BN.bn_lt_mask nLen s n in
  let h = ST.get () in
  SB.bn_lt_mask_lemma (as_seq h s) (as_seq h n);

  let res =
    if BB.unsafe_bool_of_limb mask then begin
      Math.Lemmas.pow2_le_compat (v bits * v nLen) (v modBits);
      SM.bn_precomp_r2_mod_n_lemma (v modBits - 1) (as_seq h n);

      let h0 = ST.get () in
      BE.mk_bn_mod_exp_precompr2 nLen ke.BE.exp_vt_precomp n r2 s eBits e m_def;
      let h1 = ST.get () in
      SD.bn_eval_inj (v nLen) (as_seq h1 m_def)
        (SE.bn_mod_exp_vartime_precompr2 (v nLen) (as_seq h0 n) (as_seq h0 r2)
        (as_seq h1 s) (v eBits) (as_seq h0 e));

      if bn_lt_pow2 modBits m_def then true
      else false end
    else false in
  res


inline_for_extraction noextract
let rsapss_verify_bn_to_msg_st (t:limb_t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:modBits_t t) =
    saltLen:size_t
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> m:lbignum t (blocks modBits (size (bits t))) ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h m /\ disjoint m msg /\

    LS.rsapss_verify_pre a (v saltLen) (v msgLen) (as_seq h msg))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_verify_bn_to_msg a (v modBits) (v saltLen) (v msgLen) (as_seq h0 msg) (as_seq h0 m))


inline_for_extraction noextract
val rsapss_verify_bn_to_msg:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_verify_bn_to_msg_st t a modBits

let rsapss_verify_bn_to_msg #t a modBits saltLen msgLen msg m =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in

  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in
  [@inline_let] let mLen = blocks emLen (size numb) in
  let em = create emLen (u8 0) in

  LS.blocks_bits_lemma t (v emBits);
  LS.blocks_numb_lemma t (v emBits);
  assert (SD.blocks (v emBits) bits == v mLen);
  assert (numb * v mLen <= max_size_t);
  assert (v mLen <= v nLen);

  let m1 = sub m 0ul mLen in
  BN.bn_to_bytes_be emLen m1 em;
  let res = RP.pss_verify a saltLen msgLen msg emBits em in
  pop_frame ();
  res


inline_for_extraction noextract
let rsapss_verify_compute_msg_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
   let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> sgnt:lbuffer uint8 (blocks modBits 8ul)
  -> m:lbignum t len ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h sgnt /\ live h pkey /\ live h m /\
    disjoint m sgnt /\ disjoint m pkey /\
    as_seq h m == LSeq.create (v len) (uint #t 0) /\
    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies (loc m) h0 h1 /\
    (r, as_seq h1 m) == LS.rsapss_verify_compute_msg (v modBits) (v eBits) (as_seq h0 pkey) (as_seq h0 sgnt))


inline_for_extraction noextract
val rsapss_verify_compute_msg:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:modBits_t t ->
  rsapss_verify_compute_msg_st t ke modBits

let rsapss_verify_compute_msg #t ke modBits eBits pkey sgnt m =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in
  let k = blocks modBits 8ul in

  let s = create nLen (uint #t 0) in
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v k) numb == v nLen);
  assert (numb * v nLen <= max_size_t);
  BN.bn_from_bytes_be k sgnt s;

  let b = rsapss_verify_bn #t ke modBits eBits pkey m s in
  pop_frame ();
  b


inline_for_extraction noextract
let rsapss_verify_st1 (t:limb_t) (ke:BE.exp t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:modBits_t t) =
   let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> saltLen:size_t
  -> sgnt:lbuffer uint8 (blocks modBits 8ul)
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h msg /\ live h sgnt /\ live h pkey /\
    disjoint msg sgnt /\ disjoint msg pkey /\

    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey) /\
    LS.rsapss_verify_pre a (v saltLen) (v msgLen) (as_seq h msg))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_verify_ a (v modBits) (v eBits) (as_seq h0 pkey)
      (v saltLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_verify_:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_verify_st1 t ke a modBits

let rsapss_verify_ #t ke a modBits eBits pkey saltLen sgnt msgLen msg =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  let nLen = blocks modBits (size bits) in
  let m = create nLen (uint #t 0) in
  let b = rsapss_verify_compute_msg ke modBits eBits pkey sgnt m in
  let res = if b then rsapss_verify_bn_to_msg a modBits saltLen msgLen msg m else false in
  pop_frame ();
  res


inline_for_extraction noextract
let rsapss_verify_st (t:limb_t) (ke:BE.exp t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:modBits_t t) =
   let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> saltLen:size_t
  -> sgntLen:size_t
  -> sgnt:lbuffer uint8 sgntLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h msg /\ live h sgnt /\ live h pkey /\
    disjoint msg sgnt /\ disjoint msg pkey /\

    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == LS.rsapss_verify a (v modBits) (v eBits) (as_seq h0 pkey)
      (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_verify:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_verify_st t ke a modBits

let rsapss_verify #t ke a modBits eBits pkey saltLen sgntLen sgnt msgLen msg =
  let hLen = RM.hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  //assert (max_size_t < Hash.max_input_length a);
  assert (v msgLen <= max_size_t);
  assert (v hLen + 8 < max_size_t);

  let b =
    saltLen <=. 0xfffffffful -! hLen -! 8ul &&
    sgntLen =. blocks modBits 8ul in

  if b then
    rsapss_verify_ ke a modBits eBits pkey saltLen sgnt msgLen msg
  else
    false


inline_for_extraction noextract
let rsapss_skey_sign_st (t:limb_t) (ke:BE.exp t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:size_t) =
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> db:lbuffer uint8 (blocks dBits 8ul)
  -> saltLen:size_t
  -> salt:lbuffer uint8 saltLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h ->
    blocks modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h salt /\ live h msg /\ live h sgnt /\
    live h nb /\ live h eb /\ live h db /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\
    disjoint sgnt nb /\ disjoint sgnt eb /\ disjoint sgnt db /\
    disjoint salt msg)
  (ensures  fun h0 b h1 -> modifies (loc sgnt) h0 h1 /\
   (let sgnt_s = S.rsapss_skey_sign a (v modBits) (v eBits) (v dBits)
     (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) in
    if b then Some? sgnt_s /\ as_seq h1 sgnt == Some?.v sgnt_s else None? sgnt_s))


inline_for_extraction noextract
val rsapss_skey_sign:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsapss_load_skey:RK.rsapss_load_skey_st t ke modBits
  -> rsapss_sign:rsapss_sign_st t ke a modBits ->
  rsapss_skey_sign_st t ke a modBits

let rsapss_skey_sign #t ke a modBits rsapss_load_skey rsapss_sign eBits dBits nb eb db saltLen salt msgLen msg sgnt =
  [@inline_let] let bits = size (bits t) in
  let h0 = ST.get () in
  push_frame ();
  let skey = create (2ul *! blocks modBits bits +! blocks eBits bits +! blocks dBits bits) (uint #t 0) in
  let b = rsapss_load_skey eBits dBits nb eb db skey in
  LS.rsapss_load_skey_lemma #t (v modBits) (v eBits) (v dBits) (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db);

  let res =
    if b then
      rsapss_sign eBits dBits skey saltLen salt msgLen msg sgnt
    else
      false in
  pop_frame ();
  let h1 = ST.get () in
  assert ((res, as_seq h1 sgnt) == LS.rsapss_skey_sign #t a (v modBits) (v eBits) (v dBits)
      (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db) (v saltLen) (as_seq h0 salt)
      (v msgLen) (as_seq h0 msg) (as_seq h0 sgnt));
  res


inline_for_extraction noextract
let rsapss_pkey_verify_st (t:limb_t) (ke:BE.exp t) (a:Hash.algorithm{S.hash_is_supported a}) (modBits:size_t) =
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> nb:lbuffer uint8 (blocks modBits 8ul)
  -> eb:lbuffer uint8 (blocks eBits 8ul)
  -> saltLen:size_t
  -> sgntLen:size_t
  -> sgnt:lbuffer uint8 sgntLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    blocks modBits (size (bits t)) == ke.BE.bn.BN.len /\
    live h msg /\ live h sgnt /\ live h nb /\ live h eb /\
    disjoint msg sgnt /\ disjoint nb eb /\ disjoint sgnt nb /\
    disjoint sgnt eb /\ disjoint msg nb /\ disjoint msg eb)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.rsapss_pkey_verify a (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb)
      (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_pkey_verify:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsapss_load_pkey:RK.rsapss_load_pkey_st t ke modBits
  -> rsapss_verify:rsapss_verify_st t ke a modBits ->
  rsapss_pkey_verify_st t ke a modBits

let rsapss_pkey_verify #t ke a modBits rsapss_load_pkey rsapss_verify eBits nb eb saltLen sgntLen sgnt msgLen msg =
  push_frame ();
  [@inline_let] let bits = size (bits t) in
  let pkey = create (2ul *! blocks modBits bits +! blocks eBits bits) (uint #t 0) in
  let h0 = ST.get () in
  let b = rsapss_load_pkey eBits nb eb pkey in
  LS.rsapss_load_pkey_lemma #t (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb);

  let res =
    if b then
      rsapss_verify eBits pkey saltLen sgntLen sgnt msgLen msg
    else
      false in
  pop_frame ();
  let h1 = ST.get () in
  assert (res == LS.rsapss_pkey_verify #t a (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb)
    (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg));
  res
