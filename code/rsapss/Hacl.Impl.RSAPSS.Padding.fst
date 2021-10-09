module Hacl.Impl.RSAPSS.Padding

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.RSAPSS.MGF

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module Hash = Spec.Agile.Hash
module S = Spec.RSAPSS
module BD = Hacl.Bignum.Definitions


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let salt_len_t (a:Hash.algorithm) =
  saltLen:size_t{8 + Hash.hash_length a + v saltLen <= max_size_t /\ 8 + Hash.hash_length a + v saltLen <= Hash.max_input_length a}

inline_for_extraction noextract
let msg_len_t (a:Hash.algorithm) =
  msgLen:size_t{v msgLen <= Hash.max_input_length a}

inline_for_extraction noextract
let em_len_t (a:Hash.algorithm) (saltLen:salt_len_t a) =
  emBits:size_t{0 < v emBits /\ Hash.hash_length a + v saltLen + 2 <= S.blocks (v emBits) 8}


inline_for_extraction noextract
val xor_bytes:
    len:size_t{v len > 0}
  -> b1:lbuffer uint8 len
  -> b2:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
  (ensures  fun h0 _ h1 -> modifies (loc b1) h0 h1 /\
    as_seq h1 b1 == S.xor_bytes (as_seq h0 b1) (as_seq h0 b2))

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
  -> saltLen:salt_len_t a
  -> salt:lbuffer uint8 saltLen
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
    let m1Len = 8 + Hash.hash_length a + v saltLen in
    let m1 = LSeq.create m1Len (u8 0) in
    let m1 = LSeq.update_sub m1 8 (Hash.hash_length a) mHash in
    let m1 = LSeq.update_sub m1 (8 + Hash.hash_length a) (v saltLen) (as_seq h0 salt) in
    as_seq h1 m1Hash == Hash.hash a m1))

let get_m1Hash a saltLen salt msgLen msg hLen m1Hash =
  push_frame ();
  //m1 = [8 * 0x00; mHash; salt]
  let m1Len = 8ul +! hLen +! saltLen in
  let m1 = create m1Len (u8 0) in
  let h0 = ST.get () in
  update_sub_f h0 m1 8ul hLen
    (fun h -> Hash.hash a (as_seq h0 msg))
    (fun _ -> hash a (sub m1 8ul hLen) msgLen msg);
  update_sub m1 (8ul +! hLen) saltLen salt;
  hash a m1Hash m1Len m1;
  pop_frame()


inline_for_extraction noextract
val get_maskedDB:
    a:Hash.algorithm{S.hash_is_supported a}
  -> saltLen:salt_len_t a
  -> salt:lbuffer uint8 saltLen
  -> hLen:size_t{v hLen == Hash.hash_length a}
  -> m1Hash:lbuffer uint8 hLen
  -> emBits:em_len_t a saltLen
  -> dbLen:size_t{v dbLen == S.blocks (v emBits) 8 - Hash.hash_length a - 1}
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
    let last_before_salt = dbLen - v saltLen - 1 in
    let db = LSeq.upd db last_before_salt (u8 1) in
    let db = LSeq.update_sub db (last_before_salt + 1) (v saltLen) (as_seq h0 salt) in

    let dbMask = S.mgf_hash a (v hLen) (as_seq h0 m1Hash) dbLen in
    let maskedDB = S.xor_bytes db dbMask in
    let maskedDB = S.db_zero maskedDB (v emBits) in
    as_seq h1 db_mask == maskedDB))

let get_maskedDB a saltLen salt hLen m1Hash emBits dbLen db =
  push_frame ();
  //db = [0x00;..; 0x00; 0x01; salt]
  let last_before_salt = dbLen -! saltLen -! 1ul in
  db.(last_before_salt) <- u8 1;
  update_sub db (last_before_salt +! 1ul) saltLen salt;

  let dbMask = create dbLen (u8 0) in
  assert_norm (Hash.hash_length a + 4 <= max_size_t /\ Hash.hash_length a + 4 <= Hash.max_input_length a);
  mgf_hash a hLen m1Hash dbLen dbMask;
  xor_bytes dbLen db dbMask;
  db_zero dbLen db emBits;
  pop_frame()


val pss_encode:
    a:Hash.algorithm{S.hash_is_supported a}
  -> saltLen:salt_len_t a
  -> salt:lbuffer uint8 saltLen
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> emBits:em_len_t a saltLen
  -> em:lbuffer uint8 (BD.blocks emBits 8ul) ->
  Stack unit
  (requires fun h ->
    live h salt /\ live h msg /\ live h em /\
    disjoint msg salt /\ disjoint em msg /\ disjoint em salt /\
    as_seq h em == LSeq.create (S.blocks (v emBits) 8) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc em) h0 h1 /\
    as_seq h1 em == S.pss_encode a (v saltLen) (as_seq h0 salt) (v msgLen) (as_seq h0 msg) (v emBits))

[@CInline]
let pss_encode a saltLen salt msgLen msg emBits em =
  push_frame ();
  let hLen = hash_len a in
  let m1Hash = create hLen (u8 0) in
  get_m1Hash a saltLen salt msgLen msg hLen m1Hash;

  let emLen = BD.blocks emBits 8ul in
  let dbLen = emLen -! hLen -! 1ul in
  let db = create dbLen (u8 0) in
  get_maskedDB a saltLen salt hLen m1Hash emBits dbLen db;

  update_sub em 0ul dbLen db;
  update_sub em dbLen hLen m1Hash;
  em.(emLen -! 1ul) <- u8 0xbc;
  pop_frame()


inline_for_extraction noextract
val pss_verify_:
    a:Hash.algorithm{S.hash_is_supported a}
  -> saltLen:salt_len_t a
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> emBits:em_len_t a saltLen
  -> em:lbuffer uint8 (BD.blocks emBits 8ul) ->
  Stack bool
  (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.pss_verify_ a (v saltLen) (v msgLen) (as_seq h0 msg) (v emBits) (as_seq h0 em))

let pss_verify_ a saltLen msgLen msg emBits em =
  push_frame ();
  let emLen = BD.blocks emBits 8ul in

  let hLen = hash_len a in
  let m1Hash0 = create hLen (u8 0) in
  let dbLen = emLen -! hLen -! 1ul in
  let maskedDB = sub em 0ul dbLen in
  let m1Hash = sub em dbLen hLen in

  let dbMask = create dbLen (u8 0) in
  mgf_hash a hLen m1Hash dbLen dbMask;
  xor_bytes dbLen dbMask maskedDB;
  db_zero dbLen dbMask emBits;

  let padLen = emLen -! saltLen -! hLen -! 1ul in
  let pad2 = create padLen (u8 0) in
  pad2.(padLen -! 1ul) <- u8 0x01;

  let pad = sub dbMask 0ul padLen in
  let salt = sub dbMask padLen saltLen in

  let res =
    if not (Lib.ByteBuffer.lbytes_eq #padLen pad pad2) then false
    else begin
      get_m1Hash a saltLen salt msgLen msg hLen m1Hash0;
      Lib.ByteBuffer.lbytes_eq #hLen m1Hash0 m1Hash end in
  pop_frame ();
  res


#set-options "--z3rlimit 300"

val pss_verify:
    a:Hash.algorithm{S.hash_is_supported a}
  -> saltLen:salt_len_t a
  -> msgLen:msg_len_t a
  -> msg:lbuffer uint8 msgLen
  -> emBits:size_t{0 < v emBits}
  -> em:lbuffer uint8 (BD.blocks emBits 8ul) ->
  Stack bool
  (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.pss_verify a (v saltLen) (v msgLen) (as_seq h0 msg) (v emBits) (as_seq h0 em))

[@CInline]
let pss_verify a saltLen msgLen msg emBits em =
  let emLen = BD.blocks emBits 8ul in
  let msBits = emBits %. 8ul in

  let em_0 = if msBits >. 0ul then em.(0ul) &. (u8 0xff <<. msBits) else u8 0 in
  let em_last = em.(emLen -! 1ul) in

  if (emLen <. saltLen +! hash_len a +! 2ul) then false
  else begin
    if not (FStar.UInt8.(Lib.RawIntTypes.u8_to_UInt8 em_last =^ 0xbcuy) &&
      FStar.UInt8.(Lib.RawIntTypes.u8_to_UInt8 em_0 =^ 0uy)) then false
    else pss_verify_ a saltLen msgLen msg emBits em end
