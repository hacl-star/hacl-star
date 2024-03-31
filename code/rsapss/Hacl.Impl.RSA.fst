module Hacl.Impl.RSA

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

module RK = Hacl.Impl.RSA.Keys

#reset-options "--z3rlimit 150 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let modBits_t (t:limb_t) = modBits:size_t{1 < v modBits /\ 2 * bits t * SD.blocks (v modBits) (bits t) <= max_size_t}


inline_for_extraction noextract
let rsa_dec_bn_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
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
    LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey) /\
    bn_v h m < bn_v h (gsub skey 0ul len))
  (ensures  fun h0 r h1 -> modifies (loc s |+| loc m') h0 h1 /\
    (r, as_seq h1 s) == LS.rsapss_sign_bn (v modBits) (v eBits) (v dBits) (as_seq h0 skey) (as_seq h0 m))


inline_for_extraction noextract
val rsa_dec_bn: #t:limb_t -> ke:BE.exp t -> modBits:modBits_t t -> rsa_dec_bn_st t ke modBits
let rsa_dec_bn #t ke modBits eBits dBits skey m m' s =
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
let rsa_dec_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
  let emLen = blocks (modBits -! 1ul) 8ul in
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> em:lbuffer uint8 emLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h sgnt /\ live h skey /\ live h em /\
    disjoint sgnt skey /\ disjoint em sgnt /\ disjoint em skey /\
    LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey) /\
    (let emBits = v modBits - 1 in
      if emBits % 8 > 0 then v (Seq.index (as_seq h em) 0) < pow2 (emBits % 8) else v (Seq.index (as_seq h em) 0) < pow2 8))
  (ensures  fun h0 eq_m h1 -> modifies (loc sgnt) h0 h1 /\
    (eq_m, as_seq h1 sgnt) == 
    LS.rsapss_sign_compute_sgnt #t (v modBits) (v eBits) (v dBits) (as_seq h0 skey) (as_seq h0 em))


inline_for_extraction noextract
val rsa_dec:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:modBits_t t ->
  rsa_dec_st t ke modBits

#push-options "--z3rlimit 200"
let rsa_dec #t ke modBits eBits dBits skey em sgnt =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in
  [@inline_let] let mLen = blocks emLen (size numb) in
  let k = blocks modBits 8ul in
  
  LS.blocks_bits_lemma t (v emBits);
  LS.blocks_numb_lemma t (v emBits);
  assert (SD.blocks (v emBits) bits = v mLen);
  assert (numb * v mLen <= max_size_t);
  assert (v mLen <= v nLen);

  let m = create nLen (uint #t 0) in
  let s = create nLen (uint #t 0) in
  let m' = create nLen (uint #t 0) in
  let h' = ST.get () in
  update_sub_f h' m 0ul mLen
    (fun h -> SB.bn_from_bytes_be (v emLen) (as_seq h' em))
    (fun _ -> BN.bn_from_bytes_be emLen em (sub m 0ul mLen));
  let h = ST.get() in
  assume (bn_v h m < bn_v h (gsub skey 0ul nLen));
  let eq_b = rsa_dec_bn ke modBits eBits dBits skey m m' s in
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v k) numb == v nLen);
  assert (numb * v nLen <= max_size_t);
  BN.bn_to_bytes_be k s sgnt;
  pop_frame ();
  eq_b
#pop-options


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
let rsa_enc_bn_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> s:lbignum t len
  -> m_def:lbignum t len ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h pkey /\ live h m_def /\ live h s /\
    disjoint m_def pkey /\ disjoint m_def s /\ disjoint s pkey /\
    LS.rsa_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies (loc m_def) h0 h1 /\
    (r, as_seq h1 m_def) == LS.rsapss_verify_bn (v modBits) (v eBits) (as_seq h0 pkey) (as_seq h0 m_def) (as_seq h0 s))


inline_for_extraction noextract
val rsa_enc_bn: #t:limb_t -> ke:BE.exp t -> modBits:modBits_t t -> rsa_enc_bn_st t ke modBits
let rsa_enc_bn #t ke modBits eBits pkey s m_def =
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
let rsa_enc_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
   let len = blocks modBits (size (bits t)) in
   let emLen = blocks (modBits -! 1ul) 8ul in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> sgnt:lbuffer uint8 (blocks modBits 8ul)
  -> em:lbuffer uint8 emLen ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h sgnt /\ live h pkey /\ live h em /\
    disjoint em sgnt /\ disjoint em pkey /\
    as_seq h em == LSeq.create (v emLen) (u8 0) /\
    LS.rsa_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies (loc em) h0 h1)
//    (r, as_seq h1 em) == LS.rsapss_verify_compute_msg (v modBits) (v eBits) (as_seq h0 pkey) (as_seq h0 sgnt))


inline_for_extraction noextract
val rsa_enc:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:modBits_t t ->
  rsa_enc_st t ke modBits

let rsa_enc #t ke modBits eBits pkey sgnt em =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in
  let k = blocks modBits 8ul in


  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in
  
  let s = create nLen (uint #t 0) in
  let m = create (blocks (modBits) (size bits)) (uint #t 0) in
  
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v k) numb == v nLen);
  assert (numb * v nLen <= max_size_t);
  BN.bn_from_bytes_be k sgnt s;

  let b = rsa_enc_bn #t ke modBits eBits pkey s m in

  [@inline_let] let mLen = blocks emLen (size numb) in
  let m1 = sub m 0ul mLen in
  BN.bn_to_bytes_be emLen m1 em;
  pop_frame ();
  b

