module Hacl.Impl.RSAPSS

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum
open Hacl.Bignum.Exponentiation

module ST = FStar.HyperStack.ST

module Hash = Spec.Agile.Hash
module SB = Hacl.Spec.Bignum
module BB = Hacl.Spec.Bignum.Base

module S = Spec.RSAPSS
module LS = Hacl.Spec.RSAPSS

open Hacl.Impl.RSAPSS.Padding
open Hacl.Impl.RSAPSS.MGF


#reset-options "--z3rlimit 150 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val rsapss_sign_:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{LS.skey_len_pre (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul +! blocks dBits 64ul)
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
    LS.rsapss_sign_post a (v modBits) (v eBits) (v dBits) (as_seq h0 skey)
      (v sLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) eq_m (as_seq h1 sgnt))

let rsapss_sign_ a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  push_frame ();
  let h_init = ST.get () in
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let dLen = blocks dBits 64ul in

  let n  = sub skey 0ul nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen +! nLen) eLen in
  let d  = sub skey (nLen +! nLen +! eLen) dLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m  = create nLen (u64 0) in
  let m' = create nLen (u64 0) in
  let s  = create nLen (u64 0) in

  pss_encode a sLen salt msgLen msg emBits em;
  LS.em_blocks_lt_max_size_t (v modBits);
  assert (8 * v (blocks emLen 8ul) <= max_size_t);

  let h' = ST.get () in
  update_sub_f h' m 0ul (blocks emLen 8ul)
    (fun h -> SB.bn_from_bytes_be (v emLen) (as_seq h' em))
    (fun _ -> bn_from_bytes_be emLen em (sub m 0ul (blocks emLen 8ul)));

  let _ = bn_mod_exp_mont_ladder_precompr2 nLen n m dBits d r2 s in
  let _ = bn_mod_exp_precompr2 nLen n s eBits e r2 m' in

  let eq_m = bn_eq_mask nLen m m' in
  mapT nLen s (logand eq_m) s;

  LS.blocks_bits_lemma (v modBits);
  assert (v (blocks k 8ul) == v nLen);
  bn_to_bytes_be k s sgnt;

  let h_final = ST.get () in
  LS.rsapss_sign_lemma a (v modBits) (v eBits) (v dBits)
    (as_seq h_init skey) (v sLen) (as_seq h_init salt) (v msgLen) (as_seq h_init msg);
  pop_frame ();
  BB.unsafe_bool_of_u64 eq_m


inline_for_extraction noextract
let rsapss_sign_st (a:Hash.algorithm{S.hash_is_supported a}) =
    modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{LS.skey_len_pre (v modBits) (v eBits) (v dBits)}
  -> skey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul +! blocks dBits 64ul)
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
   (let nLen = blocks modBits 64ul in
    let eLen = blocks eBits 64ul in
    let dLen = blocks dBits 64ul in

    let n = bn_v h0 (gsub skey 0ul nLen) in
    let e = bn_v h0 (gsub skey (nLen +! nLen) eLen) in
    let d = bn_v h0 (gsub skey (nLen +! nLen +! eLen) dLen) in
    let pkeys : S.rsapss_pkey (v modBits) = S.Mk_rsapss_pkey n e in
    let skeys : S.rsapss_skey (v modBits) = S.Mk_rsapss_skey pkeys d in
    let sgnt_s = S.rsapss_sign a (v modBits) skeys (v sLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) in
    if b then Some? sgnt_s /\ as_seq h1 sgnt == Some?.v sgnt_s else None? sgnt_s))


inline_for_extraction noextract
val rsapss_sign: a:Hash.algorithm{S.hash_is_supported a} -> rsapss_sign_st a
let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  let hLen = hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  assert (max_size_t < Hash.max_input_length a);

  let b =
    sLen <=. 0xfffffffful -! hLen -! 8ul &&
    sLen +! hLen +! 2ul <=. blocks (modBits -! 1ul) 8ul in

  if b then
    rsapss_sign_ a modBits eBits dBits skey sLen salt msgLen msg sgnt
  else
    false



inline_for_extraction noextract
val bn_lt_pow2:
    modBits:size_t{1 < v modBits}
  -> m:lbignum (blocks modBits 64ul) ->
  Stack bool
  (requires fun h -> live h m)
  (ensures  fun h0 r h1 -> h0 == h1 /\
    r == LS.bn_lt_pow2 (v modBits) (as_seq h0 m))

let bn_lt_pow2 modBits m =
  if not ((modBits -! 1ul) %. 8ul =. 0ul) then true
  else begin
    let get_bit = bn_get_ith_bit (blocks modBits 64ul) m (modBits -! 1ul) in
    FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 get_bit =^ 0uL) end


inline_for_extraction noextract
val rsapss_verify_:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_t
  -> eBits:size_t{LS.pkey_len_pre (v modBits) (v eBits)}
  -> pkey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul)
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
    LS.rsapss_verify_post a (v modBits) (v eBits) (as_seq h0 pkey)
      (v sLen) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg) r)

let rsapss_verify_ a modBits eBits pkey sLen sgnt msgLen msg =
  push_frame ();
  let h_init = ST.get () in
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in

  let n  = sub pkey 0ul nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen +! nLen) eLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m = create nLen (u64 0) in
  let s = create nLen (u64 0) in
  LS.blocks_bits_lemma (v modBits);
  assert (v (blocks k 8ul) == v nLen);
  bn_from_bytes_be k sgnt s;


  let mask = bn_lt_mask nLen s n in
  let res =
    if BB.unsafe_bool_of_u64 mask then begin
      let _ = bn_mod_exp_precompr2 nLen n s eBits e r2 m in
      LS.em_blocks_lt_max_size_t (v modBits);
      assert (8 * v (blocks emLen 8ul) <= max_size_t);

      if bn_lt_pow2 modBits m then begin
	let m1 = sub m 0ul (blocks emLen 8ul) in
	bn_to_bytes_be emLen m1 em;
	pss_verify a sLen msgLen msg emBits em end
      else false end
    else false in
  pop_frame ();
  //assert (res == LS.rsapss_verify_ a (v modBits) (v eBits) (as_seq h_init pkey)
    //(v sLen) (as_seq h_init sgnt) (v msgLen) (as_seq h_init msg));
  LS.rsapss_verify_lemma a (v modBits) (v eBits) (as_seq h_init pkey)
    (v sLen) (as_seq h_init sgnt) (v msgLen) (as_seq h_init msg);
  res


inline_for_extraction noextract
let rsapss_verify_st (a:Hash.algorithm{S.hash_is_supported a}) =
    modBits:size_t
  -> eBits:size_t{LS.pkey_len_pre (v modBits) (v eBits)}
  -> pkey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul)
  -> sLen:size_t
  -> k:size_t
  -> sgnt:lbuffer uint8 k
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h sgnt /\ live h pkey /\
    disjoint msg sgnt /\

    LS.rsapss_pkey_pre (v modBits) (v eBits) (as_seq h pkey))
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
   (let nLen = blocks modBits 64ul in
    let eLen = blocks eBits 64ul in

    let n = bn_v h0 (gsub pkey 0ul nLen) in
    let e = bn_v h0 (gsub pkey (nLen +! nLen) eLen) in
    let pkeys : S.rsapss_pkey (v modBits) = S.Mk_rsapss_pkey n e in
    r == S.rsapss_verify a (v modBits) pkeys (v sLen) (v k) (as_seq h0 sgnt) (v msgLen) (as_seq h0 msg)))


inline_for_extraction noextract
val rsapss_verify: a:Hash.algorithm{S.hash_is_supported a} -> rsapss_verify_st a
let rsapss_verify a modBits eBits pkey sLen k sgnt msgLen msg =
  let hLen = hash_len a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  assert (max_size_t < Hash.max_input_length a);
  assert (v msgLen <= max_size_t);

  let b =
    sLen <=. 0xfffffffful -! hLen -! 8ul &&
    k =. blocks modBits 8ul in

  if b then
    rsapss_verify_ a modBits eBits pkey sLen sgnt msgLen msg
  else
    false
