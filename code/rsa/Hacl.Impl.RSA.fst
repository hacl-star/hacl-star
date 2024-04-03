module Hacl.Impl.RSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST

module SB = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base
module SD = Hacl.Spec.Bignum.Definitions
module SM = Hacl.Spec.Bignum.Montgomery
module SE = Hacl.Spec.Bignum.Exponentiation

module BN = Hacl.Bignum
module BE = Hacl.Bignum.Exponentiation
module BM = Hacl.Bignum.Montgomery

module S = Spec.RSA
module LS = Hacl.Spec.RSA
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
    LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey))
  (ensures  fun h0 r h1 -> modifies (loc s |+| loc m') h0 h1 /\
    (r, as_seq h1 s) == LS.rsa_dec_bn (v modBits) (v eBits) (v dBits) (as_seq h0 skey) (as_seq h0 m))

#push-options "--z3rlimit 500"
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

  let h0 = ST.get () in
  assert(LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h0 skey));
  assume(bn_v h0 d < pow2 (v dBits));
  assume(bn_v h0 e < pow2 (v eBits));
  assume(disjoint s d);
  assume(disjoint m' e);
  assume(disjoint m' s);
  assume(disjoint n s);
  let lt_c = BN.bn_lt_mask nLen m n in
  SB.bn_lt_mask_lemma (as_seq h0 m) (as_seq h0 n);
  assert (lt_c == SB.bn_lt_mask (as_seq h0 m) (as_seq h0 n));
  let h1 = ST.get () in
  assert (modifies0 h0 h1);
  if BB.unsafe_bool_of_limb lt_c then begin
    assert(bn_v h1 m < bn_v h1 n);
    assert(SE.bn_mod_exp_pre (as_seq h0 n) (as_seq h0 m) (v dBits) (as_seq h0 d));
    Math.Lemmas.pow2_le_compat (bits * v nLen) (v modBits);
    SM.bn_precomp_r2_mod_n_lemma (v modBits-1) (as_seq h0 n);
    BE.mk_bn_mod_exp_precompr2 nLen ke.BE.exp_ct_precomp n r2 m dBits d s;
    let h2 = ST.get () in
    assert (modifies1 s h1 h2);
    assert(bn_v h2 s < bn_v h2 n);
    assume(SE.bn_mod_exp_pre (as_seq h2 n) (as_seq h2 s) (v eBits) (as_seq h2 e));
    BE.mk_bn_mod_exp_precompr2 nLen ke.BE.exp_vt_precomp n r2 s eBits e m';
    let h3 = ST.get () in
    assert (modifies1 m' h2 h3);
    SD.bn_eval_inj (v nLen) (as_seq h3 s)
      (SE.bn_mod_exp_consttime_precompr2 (v nLen) (as_seq h2 n) (as_seq h2 r2)
      (as_seq h2 m) (v dBits) (as_seq h2 d));
    SD.bn_eval_inj (v nLen) (as_seq h3 m')
      (SE.bn_mod_exp_vartime_precompr2 (v nLen) (as_seq h2 n) (as_seq h2 r2)
      (as_seq h3 s) (v eBits) (as_seq h2 e));
    let eq_m = BN.bn_eq_mask nLen m m' in
    mapT nLen s (logand eq_m) s;
    admit();
    BB.unsafe_bool_of_limb eq_m
    end
  else begin
    assert(bn_v h1 m >= bn_v h1 n);
    memset s (uint #t 0) nLen;
    admit();
    false
  end
#pop-options

inline_for_extraction noextract
let rsa_dec_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
  let len = blocks modBits (size (bits t)) in
  let mLen = blocks modBits 8ul in
    eBits:size_t
  -> dBits:size_t{LS.skey_len_pre t (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum t (2ul *! len +! blocks eBits (size (bits t)) +! blocks dBits (size (bits t)))
  -> cipher:lbuffer uint8 mLen
  -> msg:lbuffer uint8 mLen ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h cipher /\ live h skey /\ live h msg /\
    disjoint cipher skey /\ disjoint msg cipher /\ disjoint msg skey /\
    LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey))
  (ensures  fun h0 eq_m h1 -> modifies (loc msg) h0 h1 /\
    (eq_m, as_seq h1 msg) == 
    LS.rsa_dec_ #t (v modBits) (v eBits) (v dBits) (as_seq h0 skey) (as_seq h0 cipher))


inline_for_extraction noextract
val rsa_dec_skey:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:modBits_t t ->
  rsa_dec_st t ke modBits

#push-options "--z3rlimit 200"
let rsa_dec_skey #t ke modBits eBits dBits skey cipher msg =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in
  let k = blocks modBits 8ul in
  [@inline_let] let mLen = blocks k (size numb) in
  
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v modBits) bits = v mLen);
  assert (numb * v mLen <= max_size_t);
  assert (v mLen <= v nLen);

  let m = create nLen (uint #t 0) in
  let s = create nLen (uint #t 0) in
  let m' = create nLen (uint #t 0) in
  let h' = ST.get () in
  BN.bn_from_bytes_be k cipher m;
  let h = ST.get() in
  let eq_b = rsa_dec_bn ke modBits eBits dBits skey m m' s in
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v k) numb == v nLen);
  assert (numb * v nLen <= max_size_t);
  BN.bn_to_bytes_be k s msg;
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
  -> cipher:lbignum t len ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h pkey /\ live h cipher /\ live h s /\
    disjoint cipher pkey /\ disjoint cipher s /\ disjoint s pkey /\
    LS.rsa_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies (loc cipher) h0 h1 /\
    (r, as_seq h1 cipher) == LS.rsa_enc_bn (v modBits) (v eBits) (as_seq h0 pkey) (as_seq h0 s))

inline_for_extraction noextract
val rsa_enc_bn: #t:limb_t -> ke:BE.exp t -> modBits:modBits_t t -> rsa_enc_bn_st t ke modBits
let rsa_enc_bn #t ke modBits eBits pkey s cipher =
  [@inline_let] let bits = size (bits t) in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0ul nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen +! nLen) eLen in

  let mask = BN.bn_lt_mask nLen s n in
  let h = ST.get () in
  SB.bn_lt_mask_lemma (as_seq h s) (as_seq h n);
  assert (disjoint cipher pkey);
  assume (disjoint cipher e);

  if BB.unsafe_bool_of_limb mask then begin
     assert (bn_v h s < bn_v h n);
     Math.Lemmas.pow2_le_compat (v bits * v nLen) (v modBits);
     SM.bn_precomp_r2_mod_n_lemma (v modBits - 1) (as_seq h n);

     let h0 = ST.get () in
     assume(SE.bn_mod_exp_pre (as_seq h0 n) (as_seq h0 s) (v eBits) (as_seq h0 e));
     BE.mk_bn_mod_exp_precompr2 nLen ke.BE.exp_vt_precomp n r2 s eBits e cipher;
     let h1 = ST.get () in
     SD.bn_eval_inj (v nLen) (as_seq h1 cipher)
       (SE.bn_mod_exp_vartime_precompr2 (v nLen) (as_seq h0 n) (as_seq h0 r2)
       (as_seq h1 s) (v eBits) (as_seq h0 e));
     admit();
     true
  end
  else begin
    BN.bn_from_uint nLen (uint #t 0) cipher;
    false
  end


inline_for_extraction noextract
let rsa_enc_st (t:limb_t) (ke:BE.exp t) (modBits:modBits_t t) =
   let len = blocks modBits (size (bits t)) in
    eBits:size_t{LS.pkey_len_pre t (v modBits) (v eBits)}
  -> pkey:lbignum t (2ul *! len +! blocks eBits (size (bits t)))
  -> msg:lbuffer uint8 (blocks modBits 8ul)
  -> cipher:lbuffer uint8 (blocks modBits 8ul) ->
  Stack bool
  (requires fun h -> len == ke.BE.bn.BN.len /\
    live h msg /\ live h pkey /\ live h cipher /\
    disjoint msg cipher /\ disjoint cipher pkey /\
    LS.rsa_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies (loc cipher) h0 h1 /\
    (r, as_seq h1 cipher) == LS.rsa_enc_ (v modBits) (v eBits) (as_seq h0 pkey) (as_seq h0 msg))


inline_for_extraction noextract
val rsa_enc_pkey:
    #t:limb_t
  -> ke:BE.exp t
  -> modBits:modBits_t t ->
  rsa_enc_st t ke modBits

let rsa_enc_pkey #t ke modBits eBits pkey msg cipher =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  [@inline_let] let numb : size_pos = numbytes t in
  let nLen = blocks modBits (size bits) in
  let k = blocks modBits 8ul in

  let s = create nLen (uint #t 0) in
  let c = create (blocks (modBits) (size bits)) (uint #t 0) in
  
  LS.blocks_bits_lemma t (v modBits);
  LS.blocks_numb_lemma t (v modBits);
  assert (SD.blocks (v k) numb == v nLen);
  assert (numb * v nLen <= max_size_t);
  BN.bn_from_bytes_be k msg s;
  let b = rsa_enc_bn #t ke modBits eBits pkey s c in
  BN.bn_to_bytes_be k c cipher;
  pop_frame ();
  b

