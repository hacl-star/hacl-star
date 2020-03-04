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
module S = Spec.RSAPSS
module LSeq = Lib.Sequence


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

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
    sLen:size_t{8 + v hLen + v sLen <= max_size_t /\ 8 + v hLen + v sLen < S.max_input}
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen
  -> m1Hash:lbuffer uint8 hLen ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h m1Hash /\
    disjoint msg salt /\ disjoint m1Hash msg /\ disjoint m1Hash salt)
  (ensures  fun h0 _ h1 -> modifies (loc m1Hash) h0 h1 /\
    (let mHash = S.sha2_256 (as_seq h0 msg) in
    let m1Len = 8 + v hLen + v sLen in
    let m1 = LSeq.create m1Len (u8 0) in
    let m1 = LSeq.update_sub m1 8 (v hLen) mHash in
    let m1 = LSeq.update_sub m1 (8 + v hLen) (v sLen) (as_seq h0 salt) in
    as_seq h1 m1Hash == S.sha2_256 m1))

let get_m1Hash sLen salt msgLen msg m1Hash =
  push_frame ();
  //m1 = [8 * 0x00; mHash; salt]
  let m1Len = 8ul +! hLen +! sLen in
  let m1 = create m1Len (u8 0) in
  let h0 = ST.get () in
  update_sub_f h0 m1 8ul hLen
    (fun h -> S.sha2_256 (as_seq h0 msg))
    (fun _ -> hash_sha256 (sub m1 8ul hLen) msgLen msg);
  update_sub m1 (8ul +! hLen) sLen salt;
  hash_sha256 m1Hash m1Len m1;
  pop_frame()


inline_for_extraction noextract
val get_maskedDB:
    sLen:size_t{8 + v hLen + v sLen <= max_size_t /\ 8 + v hLen + v sLen < S.max_input}
  -> salt:lbuffer uint8 sLen
  -> m1Hash:lbuffer uint8 hLen
  -> emBits:size_t{0 < v emBits /\ v hLen + v sLen + 2 <= v (blocks emBits 8ul)}
  -> dbLen:size_t{v dbLen == v (blocks emBits 8ul -! hLen -! 1ul)}
  -> db_mask:lbuffer uint8 dbLen ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h m1Hash /\ live h db_mask /\
    disjoint m1Hash salt /\ disjoint m1Hash db_mask /\ disjoint db_mask salt /\
    as_seq h db_mask == LSeq.create (v dbLen) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc db_mask) h0 h1 /\
   (let emLen = S.blocks (v emBits) 8 in
    let dbLen = emLen - v hLen - 1 in
    let db = LSeq.create dbLen (u8 0) in
    let last_before_salt = dbLen - v sLen - 1 in
    let db = LSeq.upd db last_before_salt (u8 1) in
    let db = LSeq.update_sub db (last_before_salt + 1) (v sLen) (as_seq h0 salt) in

    let dbMask = S.mgf_sha256 (as_seq h0 m1Hash) dbLen in
    let maskedDB = S.xor_bytes db dbMask in
    let maskedDB = S.db_zero maskedDB (v emBits) in
    as_seq h1 db_mask == maskedDB))

let get_maskedDB sLen salt m1Hash emBits dbLen db =
  push_frame ();
  //db = [0x00;..; 0x00; 0x01; salt]
  let last_before_salt = dbLen -! sLen -! 1ul in
  db.(last_before_salt) <- u8 1;
  update_sub db (last_before_salt +! 1ul) sLen salt;

  let dbMask = create dbLen (u8 0) in
  assert_norm (v hLen + 4 <= max_size_t /\ v hLen + 4 < S.max_input);
  mgf_sha256 hLen m1Hash dbLen dbMask;
  xor_bytes dbLen db dbMask;
  db_zero dbLen db emBits;
  pop_frame()


val pss_encode:
    sLen:size_t{8 + v hLen + v sLen <= max_size_t /\ 8 + v hLen + v sLen < S.max_input}
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen
  -> emBits:size_t{0 < v emBits /\ v hLen + v sLen + 2 <= v (blocks emBits 8ul)}
  -> em:lbuffer uint8 (blocks emBits 8ul) ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h em /\
    disjoint msg salt /\ disjoint em msg /\ disjoint em salt /\
    as_seq h em == LSeq.create (S.blocks (v emBits) 8) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc em) h0 h1 /\
    as_seq h1 em == S.pss_encode #(v sLen) #(v msgLen) (as_seq h0 salt) (as_seq h0 msg) (v emBits))

[@CInline]
let pss_encode sLen salt msgLen msg emBits em =
  push_frame ();
  let m1Hash = create hLen (u8 0) in
  get_m1Hash sLen salt msgLen msg m1Hash;

  let emLen = blocks emBits 8ul in
  let dbLen = emLen -! hLen -! 1ul in
  let db = create dbLen (u8 0) in
  get_maskedDB sLen salt m1Hash emBits dbLen db;

  update_sub em 0ul dbLen db;
  update_sub em dbLen hLen m1Hash;
  em.(emLen -! 1ul) <- u8 0xbc;
  pop_frame()


inline_for_extraction noextract
val pss_verify_:
    sLen:size_t{8 + v hLen + v sLen <= max_size_t /\ 8 + v hLen + v sLen < S.max_input}
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen
  -> emBits:size_t{0 < v emBits /\ v (blocks emBits 8ul) >= v sLen + v hLen + 2}
  -> em:lbuffer uint8 (blocks emBits 8ul) ->
  Stack bool
  (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.pss_verify_ #(v msgLen) (v sLen) (as_seq h0 msg) (v emBits) (as_seq h0 em))

let pss_verify_ sLen msgLen msg emBits em =
  push_frame ();
  let emLen = blocks emBits 8ul in

  let dbLen = emLen -! hLen -! 1ul in
  let maskedDB = sub em 0ul dbLen in
  let m1Hash = sub em dbLen hLen in

  let dbMask = create dbLen (u8 0) in
  mgf_sha256 hLen m1Hash dbLen dbMask;
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
      let m1Hash0 = create hLen (u8 0) in
      get_m1Hash sLen salt msgLen msg m1Hash0;
      Lib.ByteBuffer.lbytes_eq #hLen m1Hash0 m1Hash end in
  pop_frame ();
  res


val pss_verify:
    sLen:size_t{8 + v hLen + v sLen <= max_size_t /\ 8 + v hLen + v sLen < S.max_input}
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen
  -> emBits:size_t{0 < v emBits}
  -> em:lbuffer uint8 (blocks emBits 8ul) ->
  Stack bool
  (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.pss_verify #(v msgLen) (v sLen) (as_seq h0 msg) (v emBits) (as_seq h0 em))

[@CInline]
let pss_verify sLen msgLen msg emBits em =
  let open Lib.RawIntTypes in
  let emLen = blocks emBits 8ul in
  let msBits = emBits %. 8ul in

  let em_0 = if msBits >. 0ul then em.(0ul) &. (u8 0xff <<. msBits) else u8 0 in
  let em_last = em.(emLen -! 1ul) in

  if (emLen <. sLen +! hLen +! 2ul) then false
  else begin
    if not (FStar.UInt8.(u8_to_UInt8 em_last =^ 0xbcuy) && FStar.UInt8.(u8_to_UInt8 em_0 =^ 0uy)) then false
    else pss_verify_ sLen msgLen msg emBits em end


inline_for_extraction noextract
val rsapss_sign:
     modBits:size_t{1 < v modBits /\ 128 * (v (blocks modBits 64ul) + 1) <= max_size_t}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits}
  -> dBits:size_t{0 < v dBits /\ v dBits <= v modBits /\ v (blocks modBits 64ul) + v (blocks eBits 64ul) + v (blocks dBits 64ul) <= max_size_t}
  -> skey:lbignum (blocks modBits 64ul +! blocks eBits 64ul +! blocks dBits 64ul)
  -> r2:lbignum (blocks modBits 64ul)
  -> sLen:size_t{v sLen + v hLen + 8 <= max_size_t /\ v sLen + v hLen + 8 < S.max_input /\ v sLen + v hLen + 2 <= v (blocks (modBits -! 1ul) 8ul)}
  -> salt:lbuffer uint8 sLen
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen
  -> sgnt:lbuffer uint8 (blocks modBits 8ul) ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h sgnt /\ live h skey /\ live h r2 /\
    disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt /\
    disjoint sgnt skey /\ disjoint sgnt r2 /\ disjoint skey r2 /\
   (let nLen = blocks modBits 64ul in
    let n = gsub skey 0ul nLen in
    bn_v h n > 0 /\ bn_v h r2 == pow2 (128 * (v nLen + 1)) % bn_v h n))
  (ensures  fun h0 _ h1 -> modifies (loc sgnt) h0 h1)
    //as_seq h1 sgnt == S.rsapss_sign #(v sLen) #(v msgLen) (v modBits) skey_s (as_seq h0 salt) (as_seq h0 msg))

let rsapss_sign modBits eBits dBits skey r2 sLen salt msgLen msg sgnt =
  push_frame ();
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let dLen = blocks dBits 64ul in

  let n = sub skey 0ul nLen in
  let e = sub skey nLen eLen in
  let d = sub skey (nLen +! eLen) dLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m = create nLen (u64 0) in
  let s = create nLen (u64 0) in

  pss_encode sLen salt msgLen msg emBits em;
  assume (8 * v (blocks emLen 8ul) <= max_size_t);
  assume (v (blocks emLen 8ul) == v nLen);
  bn_from_bytes_be emLen em m;
  let h = ST.get () in
  bn_mod_exp modBits nLen n r2 m dBits d s;
  assume (8 * v (blocks k 8ul) <= max_size_t);
  assume (v (blocks k 8ul) == v nLen);
  let h1 = ST.get () in
  assume (bn_v h1 s < pow2 (8 * v k));
  bn_to_bytes_be k s sgnt;
  pop_frame ()


inline_for_extraction noextract
val rsapss_verify:
    modBits:size_t{1 < v modBits /\ 128 * (v (blocks modBits 64ul) + 1) <= max_size_t}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ v (blocks modBits 64ul) + v (blocks eBits 64ul) <= max_size_t}
  -> pkey:lbignum (blocks modBits 64ul +! blocks eBits 64ul)
  -> r2:lbignum (blocks modBits 64ul)
  -> sLen:size_t{v sLen + v hLen + 8 <= max_size_t /\ v sLen + v hLen + 8 < S.max_input}
  -> sgnt:lbuffer uint8 (blocks modBits 8ul)
  -> msgLen:size_t{v msgLen < S.max_input}
  -> msg:lbuffer uint8 msgLen ->
  Stack bool
  (requires fun h ->
    live h msg /\ live h sgnt /\ live h pkey /\ live h r2 /\
    disjoint msg sgnt /\ disjoint pkey r2 /\
   (let nLen = blocks modBits 64ul in
    let n = gsub pkey 0ul nLen in
    bn_v h n > 0 /\ bn_v h r2 == pow2 (128 * (v nLen + 1)) % bn_v h n))
  (ensures  fun h0 r h1 -> modifies0 h0 h1)
    //r == S.rsapss_verify #(v msgLen) (v modBits) pkey_s (v sLen) (as_seq h0 msg) (as_seq h0 sgnt))

let rsapss_verify modBits eBits pkey r2 sLen sgnt msgLen msg =
  push_frame ();
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let pkeyLen = nLen +! eLen in

  let n = sub pkey 0ul nLen in
  let e = sub pkey nLen eLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -! 1ul in
  let emLen = blocks emBits 8ul in

  let em = create emLen (u8 0) in
  let m = create nLen (u64 0) in
  let s = create nLen (u64 0) in
  assume (v (blocks k 8ul) == v nLen);
  assume (8 * v (blocks k 8ul) <= max_size_t);
  bn_from_bytes_be k sgnt s;

  let res =
    if (bn_is_less nLen s n) then begin
      bn_mod_exp modBits nLen n r2 s eBits e m;
      assume (8 * v (blocks emLen 8ul) <= max_size_t);
      assume (v (blocks emLen 8ul) == v nLen);
      let h1 = ST.get () in
      assume (bn_v h1 m < pow2 (8 * v emLen));
      bn_to_bytes_be emLen m em;
      pss_verify sLen msgLen msg emBits em end
    else false in
  pop_frame ();
  res
