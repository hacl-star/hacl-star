module Hacl.Impl.RSAPSS

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum
open Hacl.Bignum.Exponentiation

open Hacl.Impl.MGF

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module LSeq = Lib.Sequence
module HS = FStar.HyperStack

module Hash = Spec.Agile.Hash
module S = Spec.RSAPSS
module LS = Hacl.Spec.RSAPSS
module SB = Hacl.Spec.Bignum
module BM = Hacl.Bignum.Montgomery
module BN = Hacl.Bignum
module SM = Hacl.Spec.Bignum.Montgomery

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let salt_len_t (a:Hash.algorithm) =
  sLen:size_t{8 + Hash.hash_length a + v sLen <= max_size_t /\ 8 + Hash.hash_length a + v sLen <= Hash.max_input_length a}

inline_for_extraction noextract
let msg_len_t (a:Hash.algorithm) =
  msgLen:size_t{v msgLen <= Hash.max_input_length a}

inline_for_extraction noextract
let em_len_t (a:Hash.algorithm) (sLen:salt_len_t a) =
  emBits:size_t{0 < v emBits /\ Hash.hash_length a + v sLen + 2 <= v (blocks emBits 8ul)}

inline_for_extraction noextract
let pkey_len_pre (modBits:size_t) (eBits:size_t) =
  1 < v modBits /\ 0 < v eBits /\
  128 * v (blocks modBits 64ul) <= max_size_t /\
  64 * v (blocks eBits 64ul) <= max_size_t /\
  2 * v (blocks modBits 64ul) + v (blocks eBits 64ul) <= max_size_t

inline_for_extraction noextract
let skey_len_pre (modBits:size_t) (eBits:size_t) (dBits:size_t) =
  pkey_len_pre modBits eBits /\
  0 < v dBits /\ 64 * v (blocks dBits 64ul) <= max_size_t /\
  2 * v (blocks modBits 64ul) + v (blocks eBits 64ul) + v (blocks dBits 64ul) <= max_size_t


val xor_bytes:
    len:size_t{v len > 0}
  -> b1:lbuffer uint8 len
  -> b2:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
  (ensures  fun h0 _ h1 -> modifies (loc b1) h0 h1 /\
    as_seq h1 b1 == S.xor_bytes (as_seq h0 b1) (as_seq h0 b2))

[@CInline]
let xor_bytes len b1 b2 =
  map2T len b1 (fun x y -> x ^. y) b1 b2

inline_for_extraction noextract
val db_zero:
    len:size_t{v len > 0}
  -> db:lbuffer uint8 len
  -> emBits:size_t ->
  Stack unit
  (requires fun h -> live h db)
  (ensures  fun h0 _ h1 -> modifies (loc db) h0 h1 /\
    as_seq h1 db == S.db_zero #(v len) (as_seq h0 db) (v emBits))

let db_zero len db emBits =
  let msBits = emBits %. 8ul in
  if msBits >. 0ul then
    db.(0ul) <- db.(0ul) &. (u8 0xff >>. (8ul -. msBits))


inline_for_extraction noextract
val get_m1Hash:
    a:Hash.algorithm{S.hash_is_supported a}
  -> sLen:salt_len_t a
  -> salt:lbuffer uint8 sLen
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> hLen:size_t{v hLen == Hash.hash_length a}
  -> m1Hash:lbuffer uint8 hLen ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h m1Hash /\
    disjoint msg salt /\ disjoint m1Hash msg /\ disjoint m1Hash salt)
  (ensures  fun h0 _ h1 -> modifies (loc m1Hash) h0 h1 /\
    (let mHash = Hash.hash a (as_seq h0 msg) in
    let m1Len = 8 + Hash.hash_length a + v sLen in
    let m1 = LSeq.create m1Len (u8 0) in
    let m1 = LSeq.update_sub m1 8 (Hash.hash_length a) mHash in
    let m1 = LSeq.update_sub m1 (8 + Hash.hash_length a) (v sLen) (as_seq h0 salt) in
    as_seq h1 m1Hash == Hash.hash a m1))

let get_m1Hash a sLen salt msgLen msg hLen m1Hash =
  push_frame ();
  //m1 = [8 * 0x00; mHash; salt]
  let m1Len = 8ul +! hLen +! sLen in
  let m1 = create m1Len (u8 0) in
  let h0 = ST.get () in
  update_sub_f h0 m1 8ul hLen
    (fun h -> Hash.hash a (as_seq h0 msg))
    (fun _ -> hash a (sub m1 8ul hLen) msgLen msg);
  update_sub m1 (8ul +! hLen) sLen salt;
  hash a m1Hash m1Len m1;
  pop_frame()


inline_for_extraction noextract
val get_maskedDB:
    a:Hash.algorithm{S.hash_is_supported a}
  -> sLen:salt_len_t a
  -> salt:lbuffer uint8 sLen
  -> hLen:size_t{v hLen == Hash.hash_length a}
  -> m1Hash:lbuffer uint8 hLen
  -> emBits:em_len_t a sLen
  -> dbLen:size_t{v dbLen == v (blocks emBits 8ul -! hash_len a -! 1ul)}
  -> db_mask:lbuffer uint8 dbLen ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h m1Hash /\ live h db_mask /\
    disjoint m1Hash salt /\ disjoint m1Hash db_mask /\ disjoint db_mask salt /\
    as_seq h db_mask == LSeq.create (v dbLen) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc db_mask) h0 h1 /\
   (let emLen = S.blocks (v emBits) 8 in
    let dbLen = emLen - Hash.hash_length a - 1 in
    let db = LSeq.create dbLen (u8 0) in
    let last_before_salt = dbLen - v sLen - 1 in
    let db = LSeq.upd db last_before_salt (u8 1) in
    let db = LSeq.update_sub db (last_before_salt + 1) (v sLen) (as_seq h0 salt) in

    let dbMask = S.mgf_hash #a (as_seq h0 m1Hash) dbLen in
    let maskedDB = S.xor_bytes db dbMask in
    let maskedDB = S.db_zero maskedDB (v emBits) in
    as_seq h1 db_mask == maskedDB))

let get_maskedDB a sLen salt hLen m1Hash emBits dbLen db =
  push_frame ();
  //db = [0x00;..; 0x00; 0x01; salt]
  let last_before_salt = dbLen -! sLen -! 1ul in
  db.(last_before_salt) <- u8 1;
  update_sub db (last_before_salt +! 1ul) sLen salt;

  let dbMask = create dbLen (u8 0) in
  assert_norm (Hash.hash_length a + 4 <= max_size_t /\ Hash.hash_length a + 4 <= Hash.max_input_length a);
  mgf_hash a hLen m1Hash dbLen dbMask;
  xor_bytes dbLen db dbMask;
  db_zero dbLen db emBits;
  pop_frame()


val pss_encode:
    a:Hash.algorithm{S.hash_is_supported a}
  -> sLen:salt_len_t a
  -> salt:lbuffer uint8 sLen
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> emBits:em_len_t a sLen
  -> em:lbuffer uint8 (blocks emBits 8ul) ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h em /\
    disjoint msg salt /\ disjoint em msg /\ disjoint em salt /\
    as_seq h em == LSeq.create (S.blocks (v emBits) 8) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc em) h0 h1 /\
    as_seq h1 em == S.pss_encode #a #(v sLen) #(v msgLen) (as_seq h0 salt) (as_seq h0 msg) (v emBits))

[@CInline]
let pss_encode a sLen salt msgLen msg emBits em =
  push_frame ();
  let hLen = hash_len a in
  let m1Hash = create hLen (u8 0) in
  get_m1Hash a sLen salt msgLen msg hLen m1Hash;

  let emLen = blocks emBits 8ul in
  let dbLen = emLen -! hLen -! 1ul in
  let db = create dbLen (u8 0) in
  get_maskedDB a sLen salt hLen m1Hash emBits dbLen db;

  update_sub em 0ul dbLen db;
  update_sub em dbLen hLen m1Hash;
  em.(emLen -! 1ul) <- u8 0xbc;
  pop_frame()


inline_for_extraction noextract
val pss_verify_:
    a:Hash.algorithm{S.hash_is_supported a}
  -> sLen:salt_len_t a
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> emBits:em_len_t a sLen
  -> em:lbuffer uint8 (blocks emBits 8ul) ->
  Stack bool
  (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.pss_verify_ #a #(v msgLen) (v sLen) (as_seq h0 msg) (v emBits) (as_seq h0 em))

let pss_verify_ a sLen msgLen msg emBits em =
  push_frame ();
  let emLen = blocks emBits 8ul in

  let hLen = hash_len a in
  let m1Hash0 = create hLen (u8 0) in
  let dbLen = emLen -! hLen -! 1ul in
  let maskedDB = sub em 0ul dbLen in
  let m1Hash = sub em dbLen hLen in

  let dbMask = create dbLen (u8 0) in
  mgf_hash a hLen m1Hash dbLen dbMask;
  xor_bytes dbLen dbMask maskedDB;
  db_zero dbLen dbMask emBits;

  let padLen = emLen -! sLen -! hLen -! 1ul in
  let pad2 = create padLen (u8 0) in
  pad2.(padLen -! 1ul) <- u8 0x01;

  let pad = sub dbMask 0ul padLen in
  let salt = sub dbMask padLen sLen in

  let res =
    if not (Lib.ByteBuffer.lbytes_eq #padLen pad pad2) then false
    else begin
      get_m1Hash a sLen salt msgLen msg hLen m1Hash0;
      Lib.ByteBuffer.lbytes_eq #hLen m1Hash0 m1Hash end in
  pop_frame ();
  res


#set-options "--z3rlimit 300"

val pss_verify:
    a:Hash.algorithm{S.hash_is_supported a}
  -> sLen:salt_len_t a
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> emBits:size_t{0 < v emBits}
  -> em:lbuffer uint8 (blocks emBits 8ul) ->
  Stack bool
  (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.pss_verify #a #(v msgLen) (v sLen) (as_seq h0 msg) (v emBits) (as_seq h0 em))

[@CInline]
let pss_verify a sLen msgLen msg emBits em =
  let emLen = blocks emBits 8ul in
  let msBits = emBits %. 8ul in

  let em_0 = if msBits >. 0ul then em.(0ul) &. (u8 0xff <<. msBits) else u8 0 in
  let em_last = em.(emLen -! 1ul) in

  if (emLen <. sLen +! hash_len a +! 2ul) then false
  else begin
    if not (FStar.UInt8.(Lib.RawIntTypes.u8_to_UInt8 em_last =^ 0xbcuy) &&
      FStar.UInt8.(Lib.RawIntTypes.u8_to_UInt8 em_0 =^ 0uy)) then false
    else pss_verify_ a sLen msgLen msg emBits em end


inline_for_extraction noextract
let rsapss_sign_st (a:Hash.algorithm{S.hash_is_supported a}) =
    modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{skey_len_pre modBits eBits dBits}
  -> skey:lbignum (2ul *! blocks modBits 64ul +! blocks eBits 64ul +! blocks dBits 64ul)
  -> sLen:size_t
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
    disjoint sgnt salt /\ disjoint sgnt msg /\ disjoint sgnt salt /\ disjoint sgnt skey /\
    disjoint salt msg /\

    LS.rsapss_sign_pre a (v modBits) (v eBits) (v dBits) (as_seq h skey)
      (v sLen) (as_seq h salt) (v msgLen) (as_seq h msg))
  (ensures  fun h0 _ h1 -> modifies (loc sgnt) h0 h1 /\
    LS.rsapss_sign_post a (v modBits) (v eBits) (v dBits) (as_seq h0 skey)
      (v sLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) (as_seq h1 sgnt))


inline_for_extraction noextract
val rsapss_sign: a:Hash.algorithm{S.hash_is_supported a} -> rsapss_sign_st a
let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  push_frame ();
  let h_init = ST.get () in
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let dLen = blocks dBits 64ul in

  let n  = sub skey 0ul nLen in
  let r2 = sub skey nLen nLen in
  let d  = sub skey (nLen +! nLen +! eLen) dLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m = create nLen (u64 0) in
  let s = create nLen (u64 0) in

  pss_encode a sLen salt msgLen msg emBits em;
  LS.em_blocks_lt_max_size_t (v modBits);
  assert (8 * v (blocks emLen 8ul) <= max_size_t);

  let h' = ST.get () in
  update_sub_f h' m 0ul (blocks emLen 8ul)
    (fun h -> SB.bn_from_bytes_be (v emLen) (as_seq h' em))
    (fun _ -> bn_from_bytes_be emLen em (sub m 0ul (blocks emLen 8ul)));

  let _ = bn_mod_exp_mont_ladder_precompr2 nLen n m dBits d r2 s in
  LS.blocks_bits_lemma (v modBits);
  assert (v (blocks k 8ul) == v nLen);
  bn_to_bytes_be k s sgnt;
  let h_final = ST.get () in
  assert (as_seq h_final sgnt == LS.rsapss_sign a (v modBits) (v eBits) (v dBits)
    (as_seq h_init skey) (v sLen) (as_seq h_init salt) (v msgLen) (as_seq h_init msg));
  LS.rsapss_sign_lemma a (v modBits) (v eBits) (v dBits)
    (as_seq h_init skey) (v sLen) (as_seq h_init salt) (v msgLen) (as_seq h_init msg);
  pop_frame ()


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
let rsapss_verify_st (a:Hash.algorithm{S.hash_is_supported a}) =
    modBits:size_t
  -> eBits:size_t{pkey_len_pre modBits eBits}
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


inline_for_extraction noextract
val rsapss_verify: a:Hash.algorithm{S.hash_is_supported a} -> rsapss_verify_st a
let rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg =
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
    if FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB) then begin
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
  assert (res == LS.rsapss_verify a (v modBits) (v eBits) (as_seq h_init pkey)
    (v sLen) (as_seq h_init sgnt) (v msgLen) (as_seq h_init msg));
  LS.rsapss_verify_lemma a (v modBits) (v eBits) (as_seq h_init pkey)
    (v sLen) (as_seq h_init sgnt) (v msgLen) (as_seq h_init msg);
  res


//pkey = [n; r2; e]
inline_for_extraction noextract
let rsapss_load_pkey_st =
    modBits:size_t
  -> eBits:size_t{pkey_len_pre modBits eBits}
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


//skey = [pkey; d]
inline_for_extraction noextract
let rsapss_load_skey_st =
    modBits:size_t
  -> eBits:size_t
  -> dBits:size_t{skey_len_pre modBits eBits dBits}
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
      pkey_len_pre modBits eBits /\
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
      skey_len_pre modBits eBits dBits /\
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
