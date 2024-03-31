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
module RK = Hacl.Impl.RSA.Keys
open Hacl.Impl.RSA

#reset-options "--z3rlimit 150 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let rsapss_encode_msg_st (t:limb_t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
  let len = blocks (modBits -! 1ul) 8ul in
    saltLen:size_t
  -> salt:lbuffer uint8 saltLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> em:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h em /\
    disjoint salt msg /\ disjoint em msg /\ disjoint em salt /\
    as_seq h em == LSeq.create (v len) (u8 0) /\
    LS.rsapss_sign_pre a (v modBits) (v saltLen) (as_seq h salt) (v msgLen) (as_seq h msg))
  (ensures  fun h0 _ h1 -> modifies (loc em) h0 h1 /\
    as_seq h1 em == LS.rsapss_encode_msg a (v modBits) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_encode_msg:
    #t:limb_t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t ->
    rsapss_encode_msg_st t a modBits

let rsapss_encode_msg #t a modBits saltLen salt msgLen msg em =
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in
  RP.pss_encode a saltLen salt msgLen msg emBits em



inline_for_extraction noextract
let rsapss_sign_st1 (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
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

    LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey) /\
    LS.rsapss_sign_pre a (v modBits) (v saltLen) (as_seq h salt) (v msgLen) (as_seq h msg))
  (ensures  fun h0 eq_m h1 -> modifies (loc sgnt) h0 h1 /\
    (eq_m, as_seq h1 sgnt) == LS.rsapss_sign_ a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_sign_:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsa_dec:rsa_dec_st t ke modBits ->
  rsapss_sign_st1 t ke a modBits

let rsapss_sign_ #t ke a modBits rsa_dec eBits dBits skey saltLen salt msgLen msg sgnt =
  push_frame (); 
  let emLen = blocks (modBits -! 1ul) 8ul in
  let em = create emLen (u8 0) in
  rsapss_encode_msg a modBits saltLen salt msgLen msg em;
  let eq_b = rsa_dec eBits dBits skey em sgnt in
  pop_frame ();
  eq_b


inline_for_extraction noextract
let rsapss_sign_st (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
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

    LS.rsa_skey_pre (v modBits) (v eBits) (v dBits) (as_seq h skey))
  (ensures  fun h0 b h1 -> modifies (loc sgnt) h0 h1 /\
    (b, as_seq h1 sgnt) == LS.rsapss_sign a (v modBits) (v eBits) (v dBits)
      (as_seq h0 skey) (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) (as_seq h0 sgnt))


inline_for_extraction noextract
val rsapss_sign:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsa_dec:rsa_dec_st t ke modBits ->
  rsapss_sign_st t ke a modBits

let rsapss_sign #t ke a modBits rsa_dec eBits dBits skey saltLen salt msgLen msg sgnt =
  let hLen = RM.hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  //assert (max_size_t < Hash.max_input_length a);

  let b =
    saltLen <=. 0xfffffffful -! hLen -! 8ul &&
    saltLen +! hLen +! 2ul <=. blocks (modBits -! 1ul) 8ul in

  if b then
    rsapss_sign_ ke a modBits rsa_dec eBits dBits skey saltLen salt msgLen msg sgnt
  else
    false

inline_for_extraction noextract
let rsapss_verify_msg_st (t:limb_t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
  let emLen = blocks (modBits -! 1ul) 8ul in
    saltLen:size_t
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> em:lbuffer uint8 emLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h em /\ disjoint em msg /\

    LS.rsapss_verify_pre a (v saltLen) (v msgLen) (as_seq h msg))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 )
//    r == LS.rsapss_verify_bn_to_msg a (v modBits) (v saltLen) (v msgLen) (as_seq h0 msg) (as_seq h0 em))


inline_for_extraction noextract
val rsapss_verify_msg:
    #t:limb_t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t ->
  rsapss_verify_msg_st t a modBits

let rsapss_verify_msg #t a modBits saltLen msgLen msg em =
  let emBits = modBits -! 1ul in
  let res = RP.pss_verify a saltLen msgLen msg emBits em in
  res


inline_for_extraction noextract
let rsapss_verify_st1 (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
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

    LS.rsa_pkey_pre (v modBits) (v eBits) (as_seq h pkey) /\
    LS.rsapss_verify_pre a (v saltLen) (v msgLen) (as_seq h msg))
  (ensures  fun h0 r h1 -> modifies0 h0 h1)
//    r == LS.rsapss_verify_ a (v modBits) (v eBits) (as_seq h0 pkey)
//      (v saltLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_verify_:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsa_enc: rsa_enc_st t ke modBits ->
  rsapss_verify_st1 t ke a modBits

let rsapss_verify_ #t ke a modBits rsa_enc eBits pkey saltLen sgnt msgLen msg =
  push_frame ();
  [@inline_let] let bits : size_pos = bits t in
  let nLen = blocks modBits (size bits) in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in
  let em = create emLen (u8 0) in
  let b = rsa_enc eBits pkey sgnt em in
  let res = if b then rsapss_verify_msg a modBits saltLen msgLen msg em else false in
  pop_frame ();
  res


inline_for_extraction noextract
let rsapss_verify_st (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:modBits_t t) =
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

    LS.rsa_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies0 h0 h1)
//    r == LS.rsapss_verify a (v modBits) (v eBits) (as_seq h0 pkey)
//      (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_verify:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsa_enc: rsa_enc_st t ke modBits ->
  rsapss_verify_st t ke a modBits

let rsapss_verify #t ke a modBits rsa_enc eBits pkey saltLen sgntLen sgnt msgLen msg =
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
    rsapss_verify_ ke a modBits rsa_enc eBits pkey saltLen sgnt msgLen msg
  else
    false


inline_for_extraction noextract
let rsapss_skey_sign_st (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:size_t) =
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
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsa_load_skey:RK.rsa_load_skey_st t ke modBits
  -> rsapss_sign:rsapss_sign_st t ke a modBits ->
  rsapss_skey_sign_st t ke a modBits

let rsapss_skey_sign #t ke a modBits rsa_load_skey rsapss_sign eBits dBits nb eb db saltLen salt msgLen msg sgnt =
  [@inline_let] let bits = size (bits t) in
  let h0 = ST.get () in
  push_frame ();
  let skey = create (2ul *! blocks modBits bits +! blocks eBits bits +! blocks dBits bits) (uint #t 0) in
  let b = rsa_load_skey eBits dBits nb eb db skey in
  LS.rsa_load_skey_lemma #t (v modBits) (v eBits) (v dBits) (as_seq h0 nb) (as_seq h0 eb) (as_seq h0 db);

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
let rsapss_pkey_verify_st (t:limb_t) (ke:BE.exp t) (a:Hash.hash_alg{S.hash_is_supported a}) (modBits:size_t) =
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
  (ensures  fun h0 r h1 -> modifies0 h0 h1)
  ///\
  //  r == S.rsapss_pkey_verify a (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb)
  //    (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg))


inline_for_extraction noextract
val rsapss_pkey_verify:
    #t:limb_t
  -> ke:BE.exp t
  -> a:Hash.hash_alg{S.hash_is_supported a}
  -> modBits:modBits_t t
  -> rsa_load_pkey:RK.rsa_load_pkey_st t ke modBits
  -> rsapss_verify:rsapss_verify_st t ke a modBits ->
  rsapss_pkey_verify_st t ke a modBits

let rsapss_pkey_verify #t ke a modBits rsa_load_pkey rsapss_verify eBits nb eb saltLen sgntLen sgnt msgLen msg =
  push_frame ();
  [@inline_let] let bits = size (bits t) in
  let pkey = create (2ul *! blocks modBits bits +! blocks eBits bits) (uint #t 0) in
  let h0 = ST.get () in
  let b = rsa_load_pkey eBits nb eb pkey in
  LS.rsa_load_pkey_lemma #t (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb);

  let res =
    if b then
      rsapss_verify eBits pkey saltLen sgntLen sgnt msgLen msg
    else
      false in
  pop_frame ();
  let h1 = ST.get () in
//  assert (res == LS.rsapss_pkey_verify #t a (v modBits) (v eBits) (as_seq h0 nb) (as_seq h0 eb)
//    (v saltLen) (v sgntLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg));
  res
