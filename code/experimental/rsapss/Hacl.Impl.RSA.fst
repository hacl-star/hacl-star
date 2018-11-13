module Hacl.Impl.RSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Lib
open Hacl.Impl.MGF
open Hacl.Impl.Comparison
open Hacl.Impl.Convert
open Hacl.Impl.Exponentiation
open Hacl.Impl.Addition
open Hacl.Impl.Multiplication

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction
let hLen = 32ul

val xor_bytes:
    len:size_t
  -> b1:lbytes len
  -> b2:lbytes len
  -> Stack unit
    (requires fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer b1) h0 h1)
[@"c_inline"]
let xor_bytes len b1 b2 =
  let h0 = ST.get () in
  let inv h1 i = modifies (loc_buffer b1) h0 h1 in
  Lib.Loops.for 0ul len inv
  (fun i -> b1.(i) <- b1.(i) ^. b2.(i))

val pss_encode:
    sLen:size_t{8 + v hLen + v sLen < max_size_t}
  -> salt:lbytes sLen
  -> msgLen:size_t
  -> msg:lbytes msgLen
  -> emBits:size_t{v emBits > 0 /\ v hLen + v sLen + 2 <= v (blocks emBits 8ul)}
  -> em:lbytes (blocks emBits 8ul)
  -> Stack unit
    (requires fun h ->
      live h salt /\ live h msg /\ live h em /\
      disjoint msg salt /\ disjoint em msg /\ disjoint em salt)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer em) h0 h1)
[@"c_inline"]
let pss_encode sLen salt msgLen msg emBits em = admit();
  push_frame ();
  let emLen = blocks emBits 8ul in
  let msBits = emBits %. 8ul in

  let m1Len = 8ul +. hLen +. sLen in
  let dbLen = emLen -. hLen -. 1ul in
  //st = [hash(msg); m1; hash(m1); db; dbMask]
  assume (2 * v hLen + 4 + v (blocks dbLen hLen) * v hLen < pow2 32); //for mgf
  assume (v hLen + v sLen + 6 + 2 * v emLen < max_size_t);
  let stLen = hLen +. m1Len +. hLen +. dbLen +. dbLen in
  let st = create stLen (u8 0) in

  let mHash = sub st 0ul hLen in
  let m1 = sub st hLen m1Len in
  let m1Hash = sub st (hLen +. m1Len) hLen in
  let db = sub st (hLen +. m1Len +. hLen) dbLen in
  let dbMask = sub #_ #(v stLen) st (stLen -. dbLen) dbLen in

  hash_sha256 mHash msgLen msg;
  let m1_hash = sub m1 8ul hLen in
  copy m1_hash hLen mHash;
  let m1_salt = sub m1 (8ul +. hLen) sLen in
  copy m1_salt sLen salt;
  hash_sha256 m1Hash m1Len m1;

  assert (0 <= v dbLen - v sLen - 1);
  let last_before_salt = dbLen -. sLen -. 1ul in
  db.(last_before_salt) <- u8 1;
  let db_salt = sub db (last_before_salt +. 1ul) sLen in
  copy db_salt sLen salt;
  mgf_sha256 hLen m1Hash dbLen dbMask;
  xor_bytes dbLen db dbMask;

  (if msBits >. 0ul then begin
    let shift_bits = 8ul -. msBits in
    assert (0 < v shift_bits /\ v shift_bits < 8);
    db.(0ul) <- db.(0ul) &. (u8 0xff >>. shift_bits)
  end);

  let em_db = sub em 0ul dbLen in
  copy em_db dbLen db;
  let em_hash = sub em dbLen hLen in
  copy em_hash hLen m1Hash;
  em.(emLen -. 1ul) <- u8 0xbc;
  pop_frame ()

val pss_verify:
    sLen:size_t{8 + v hLen + v sLen < max_size_t}
  -> msgLen:size_t
  -> msg:lbytes msgLen
  -> emBits:size_t{v emBits > 0 /\ v hLen + v sLen + 2 <= v (blocks emBits 8ul)}  // <- check the last condition before calling this function!
  -> em:lbytes (blocks emBits 8ul)
  -> Stack bool
    (requires fun h -> live h msg /\ live h em /\ disjoint em msg)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1)
[@"c_inline"]
let pss_verify sLen msgLen msg emBits em = admit();
  push_frame ();
  let emLen = blocks emBits 8ul in
  let msBits = emBits %. 8ul in

  let em_0 = if msBits >. 0ul then em.(0ul) &. (u8 0xff <<. msBits) else u8 0 in
  let em_last = em.(emLen -. 1ul) in

  let padLen = emLen -. sLen -. hLen -. 1ul in
  let dbLen = emLen -. hLen -. 1ul in
  let m1Len = 8ul +. hLen +. sLen in
  assume (4 + 2 * v hLen + v hLen * v (blocks dbLen hLen) < max_size_t);
  //st = [hash(msg); pad; dbMask; m1; hash(m1)]
  let stLen = hLen +. padLen +. dbLen +. m1Len +. hLen in
  let st = create stLen (u8 0) in
  let res =
    if not ((eq_u8 em_0 (u8 0)) && (eq_u8 em_last (u8 0xbc))) then false
    else begin
      let mHash = sub st 0ul hLen in
      let pad2 = sub st hLen padLen in
      let dbMask = sub st (hLen +. padLen) dbLen in
      let m1 = sub st (hLen +. padLen +. dbLen) m1Len in
      let m1Hash' = sub #_ #(v stLen) st (stLen -. hLen) hLen in

      let maskedDB = sub em 0ul dbLen in
      let m1Hash = sub em dbLen hLen in

      hash_sha256 mHash msgLen msg;

      mgf_sha256 hLen m1Hash dbLen dbMask;
      xor_bytes dbLen dbMask maskedDB;
      (if msBits >. 0ul then begin
        let shift_bits = 8ul -. msBits in
        dbMask.(0ul) <- dbMask.(0ul) &. (u8 0xff >>. shift_bits)
      end);

      pad2.(padLen -. 1ul) <- u8 0x01;
      let pad = sub dbMask 0ul padLen in
      let salt = sub dbMask padLen sLen in

      let m1_hash = sub m1 8ul hLen in
      copy m1_hash hLen mHash;
      let m1_salt = sub m1 (8ul +. hLen) sLen in
      copy #_ #(v sLen) m1_salt sLen salt;
      hash_sha256 m1Hash' m1Len m1;

      if not (Lib.ByteBuffer.lbytes_eq #padLen pad pad2) then false
      else Lib.ByteBuffer.lbytes_eq #hLen m1Hash m1Hash'
    end in
  pop_frame ();
  res

inline_for_extraction noextract
val rsa_sign:
    pow2_i:size_t
  -> modBits:size_t{0 < v modBits}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits}
  -> dBits:size_t{0 < v dBits /\ v dBits <= v modBits}
  -> pLen:size_t
  -> qLen:size_t{v (blocks modBits 64ul) + v (blocks eBits 64ul) + v (blocks dBits 64ul) + v pLen + v qLen < max_size_t}
  -> skey:lbignum (blocks modBits 64ul +. blocks eBits 64ul +. blocks dBits 64ul +. pLen +. qLen)
  -> rBlind:uint64
  -> sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits 8ul) - v sLen - v hLen - 2 >= 0}
  -> salt:lbytes sLen
  -> msgLen:size_t
  -> msg:lbytes msgLen
  -> sgnt:lbytes (blocks modBits 8ul)
  -> Stack unit
    (requires fun h ->
      live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
      disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt)
    (ensures  fun h0 _ h1 -> modifies (loc_buffer sgnt) h0 h1)
let rsa_sign pow2_i modBits eBits dBits pLen qLen skey rBlind sLen salt msgLen msg sgnt =
  admit();
  push_frame ();
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let dLen = blocks dBits 64ul in
  let pkeyLen = nLen +. eLen +. nLen in
  let skeyLen = pkeyLen +. dLen +. pLen +. qLen in

  let n = sub skey 0ul nLen in
  let e = sub #_ #(v skeyLen) #(v eLen) skey nLen eLen in
  let r2 = sub skey (nLen +. eLen) nLen in
  let d = sub skey pkeyLen dLen in
  let p = sub skey (pkeyLen +. dLen) pLen in
  let q = sub skey (pkeyLen +. dLen +. pLen) qLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -. 1ul in
  let emLen = blocks emBits 8ul in

  assume (2 * v nLen + 2 * (v pLen + v qLen) + 1 < max_size_t);
  let n2Len = nLen +. nLen in
  let pqLen = pLen +. qLen in
  let stLen = n2Len +. pqLen +. pqLen +. 2ul in
  let em = create emLen (u8 0) in
  let tmp = create stLen (u64 0) in
  pss_encode sLen salt msgLen msg emBits em;

  let m = sub tmp 0ul nLen in
  let s = sub tmp nLen nLen in
  let phi_n = sub tmp n2Len pqLen in
  let p1 = sub tmp (n2Len +. pqLen) pLen in
  let q1 = sub tmp (n2Len +. pqLen +. pLen) qLen in
  let dLen' = pLen +. qLen +. 1ul in
  let d' = sub tmp (n2Len +. pqLen) dLen' in
  let bn1_start = n2Len +. pqLen +. pLen +. qLen +. 1ul in
  let bn1 = sub #_ #(v stLen) tmp bn1_start 1ul in

  text_to_nat emLen em m;
  bn1.(0ul) <- u64 1;
  let _ = bn_sub pLen p 1ul bn1 p1 in // p1 = p - 1
  let _ = bn_sub qLen q 1ul bn1 q1 in // q1 = q - 1
  bn_mul pLen p1 qLen q1 phi_n; // phi_n = p1 * q1
  bn1.(0ul) <- rBlind;
  bn_mul pqLen phi_n 1ul bn1 d'; //d' = phi_n * rBlind
  assume (v dLen <= v dLen' /\ v dLen' * 64 < max_size_t);
  let _ = bn_add dLen' d' dLen d d' in //d' = d' + d
  assume (v nLen = v (blocks modBits 64ul));
  mod_exp pow2_i modBits nLen n r2 m (dLen' *. 64ul) d' s;
  nat_to_text k s sgnt;
  pop_frame ()

inline_for_extraction noextract
val rsa_verify:
    pow2_i:size_t
  -> modBits:size_t{0 < v modBits}
  -> eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ v (blocks modBits 64ul) + v (blocks eBits 64ul) < max_size_t}
  -> pkey:lbignum (blocks modBits 64ul +. blocks eBits 64ul)
  -> sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits 8ul) - v sLen - v hLen - 2 >= 0}
  -> sgnt:lbytes (blocks modBits 8ul)
  -> msgLen:size_t
  -> msg:lbytes msgLen
  -> Stack bool
    (requires fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt)
    (ensures  fun h0 _ h1 -> modifies loc_none h0 h1)
let rsa_verify pow2_i modBits eBits pkey sLen sgnt msgLen msg =
  admit();
  push_frame ();
  let nLen = blocks modBits 64ul in
  let eLen = blocks eBits 64ul in
  let pkeyLen = nLen +. eLen +. nLen in

  let n = sub pkey 0ul nLen in
  let e = sub pkey nLen eLen in
  let r2 = sub pkey (nLen +. eLen) nLen in

  let k = blocks modBits 8ul in
  let emBits = modBits -. 1ul in
  let emLen = blocks emBits 8ul in

  let n2Len = nLen +. nLen in
  let tmp = create n2Len (u64 0) in
  let em = create k (u8 0) in

  let m = sub tmp 0ul nLen in
  let s = sub #_ #(v n2Len) tmp nLen nLen in
  text_to_nat k sgnt s;

  let res =
    if (bn_is_less nLen s nLen n) then begin
      mod_exp pow2_i modBits nLen n r2 s eBits e m;
      nat_to_text emLen m em;
      pss_verify sLen msgLen msg emBits em end
    else false in
  pop_frame ();
  res
