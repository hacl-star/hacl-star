module Spec.RSAPSS

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes

open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators
open Lib.NatMod

module Hash = Spec.SHA2

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let size_pos = x:size_nat{x > 0}

val blocks:
     x:size_pos
  -> m:size_pos
  -> r:size_pos{x <= m * r}
let blocks x m = (x - 1) / m + 1

val xor_bytes:
     #len:size_pos
  -> b1:lbytes len
  -> b2:lbytes len
  -> lbytes len
let xor_bytes #len b1 b2 =
  map2 (fun x y -> x ^. y) b1 b2

val eq_bytes:
    #len:size_nat
  -> b1:lbytes len
  -> b2:lbytes len
  -> bool
let eq_bytes #len b1 b2 = lbytes_eq b1 b2
//for_all2 (fun x y -> uint_to_nat #U8 x = uint_to_nat #U8 y) b1 b2

(* SHA256 *)
let max_input_len_sha256 = pow2 61
let hLen = 32

val hash_sha256:
    #len:size_nat{len < max_input_len_sha256}
  -> msg:lbytes len
  -> lbytes hLen
let hash_sha256 #len msg =
  Hash.hash256 msg

(* Mask Generation Function *)
(* max_size_t = pow2 32 - 1 *)
val mgf_sha256:
     #len:size_nat{len + 4 < max_size_t /\ len + 4 < max_input_len_sha256}
  -> mgfseed:lbytes len
  -> maskLen:size_pos{(blocks maskLen hLen) * hLen < pow2 32}
  -> lbytes maskLen
let mgf_sha256 #len mgfseed maskLen =
  let n = blocks maskLen hLen in
  let acc = create (n * hLen) (u8 0) in

  let mgfseed_counter = create (len + 4) (u8 0) in
  let mgfseed_counter = update_sub mgfseed_counter 0 len mgfseed in

  let acc =
    repeati n
    (fun i acc ->
      let counter = nat_to_bytes_be 4 i in
      let mgfseed_counter = update_sub mgfseed_counter len 4 counter in
      let mHash = hash_sha256 mgfseed_counter in
      update_sub acc (hLen * i) hLen mHash
    ) acc in
  sub acc 0 maskLen

(* Bignum convert functions *)
val os2ip:
    #len:size_nat
  -> b:lbytes len
  -> res:nat{res < pow2 (8 * len)}
let os2ip #len b = nat_from_bytes_be b

val i2osp:
     #len:size_nat
  -> n:nat{n < pow2 (8 * len)}
  -> lbytes len
let i2osp #len n = nat_to_bytes_be len n

(* RSA *)
type modBits = modBits:size_nat{1 < modBits}

noeq type rsa_pubkey (modBits:modBits) =
  | Mk_rsa_pubkey: n:nat{1 < n /\ pow2 (modBits - 1) <= n /\ n < pow2 modBits}
                -> e:nat_mod n{1 < nat_mod_v e}
                -> rsa_pubkey modBits

noeq type rsa_privkey (modBits:modBits) =
  | Mk_rsa_privkey: pkey:rsa_pubkey modBits
                 -> d:nat_mod (Mk_rsa_pubkey?.n pkey){1 < nat_mod_v d}
                 -> rsa_privkey modBits

val db_zero:
     #len:size_pos
  -> db:lbytes len
  -> emBits:size_nat
  -> lbytes len
let db_zero #len db emBits =
  let msBits = emBits % 8 in
  if msBits > 0 then
    db.[0] <- db.[0] &. (u8 0xff >>. size (8 - msBits))
  else db

val pss_encode:
     #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> salt:lbytes sLen
  -> msg:lbytes msgLen
  -> emBits:size_pos{hLen + sLen + 2 <= blocks emBits 8}
  -> lbytes (blocks emBits 8)
let pss_encode #sLen #msgLen salt msg emBits =
  let mHash = hash_sha256 msg in

  //m1 = [8 * 0x00; mHash; salt]
  let m1Len = 8 + hLen + sLen in
  let m1 = create m1Len (u8 0) in
  let m1 = update_sub m1 8 hLen mHash in
  let m1 = update_sub m1 (8 + hLen) sLen salt in
  let m1Hash = hash_sha256 m1 in

  //db = [0x00;..; 0x00; 0x01; salt]
  let emLen = blocks emBits 8 in
  let dbLen = emLen - hLen - 1 in
  let db = create dbLen (u8 0) in
  let last_before_salt = dbLen - sLen - 1 in
  let db = db.[last_before_salt] <- u8 1 in
  let db = update_sub db (last_before_salt + 1) sLen salt in

  let dbMask = mgf_sha256 m1Hash dbLen in
  let maskedDB = xor_bytes db dbMask in
  let maskedDB = db_zero maskedDB emBits in

  //em = [maskedDB; m1Hash; 0xbc]
  let em = create emLen (u8 0) in
  let em = update_sub em 0 dbLen maskedDB in
  let em = update_sub em dbLen hLen m1Hash in
  em.[emLen - 1] <- u8 0xbc

val pss_verify:
     #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> msg:lbytes msgLen
  -> emBits:size_pos
  -> em:lbytes (blocks emBits 8)
  -> bool
let pss_verify #msgLen sLen msg emBits em =
  let mHash = hash_sha256 msg in

  let emLen = blocks emBits 8 in
  let msBits = emBits % 8 in

  let em_0 = if msBits > 0 then em.[0] &. (u8 0xff <<. size msBits) else u8 0 in
  let em_last = em.[emLen - 1] in

  if (emLen < sLen + hLen + 2) then false
  else begin
    if (not (uint_to_nat #U8 em_last = 0xbc && uint_to_nat #U8 em_0 = 0)) then false
    else begin
      let dbLen = emLen - hLen - 1 in
      let maskedDB = sub em 0 dbLen in
      let m1Hash = sub em dbLen hLen in

      let dbMask = mgf_sha256 m1Hash dbLen in
      let db = xor_bytes maskedDB dbMask in
      let db = db_zero db emBits in

      let padLen = emLen - sLen - hLen - 1 in
      let pad2 = create padLen (u8 0) in
      let pad2 = pad2.[padLen - 1] <- u8 0x01 in

      let pad  = sub db 0 padLen in
      let salt = sub db padLen sLen in

      if not (eq_bytes pad pad2) then false
      else begin
	let m1Len = 8 + hLen + sLen in
	let m1 = create m1Len (u8 0) in
	let m1 = update_sub m1 8 hLen mHash in
	let m1 = update_sub m1 (8 + hLen) sLen salt in
	let m1Hash0 = hash_sha256 m1 in
	eq_bytes m1Hash0 m1Hash
      end
    end
  end


val rsapss_sign:
     #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> modBits:modBits{sLen + hLen + 2 <= blocks (modBits - 1) 8}
  -> skey:rsa_privkey modBits
  -> salt:lbytes sLen
  -> msg:lbytes msgLen
  -> lbytes (blocks modBits 8)
let rsapss_sign #sLen #msgLen modBits skey salt msg =
  let pkey = Mk_rsa_privkey?.pkey skey in
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let d = Mk_rsa_privkey?.d skey in

  let nLen = blocks modBits 8 in
  FStar.Math.Lemmas.pow2_le_compat (8 * nLen) modBits;

  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = pss_encode salt msg emBits in
  let m = os2ip #emLen em in
  assume (m < n);
  let m = modulo m n in
  let s = m **% d in
  i2osp #nLen s

val rsapss_verify:
     #msgLen:size_nat{msgLen < max_input_len_sha256}
  -> modBits:modBits
  -> pkey:rsa_pubkey modBits
  -> sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256}
  -> msg:lbytes msgLen
  -> sgnt:lbytes (blocks modBits 8)
  -> bool
let rsapss_verify #msgLen modBits pkey sLen msg sgnt =
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let nLen = blocks modBits 8 in
  FStar.Math.Lemmas.pow2_le_compat (8 * nLen) modBits;

  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let s = os2ip #nLen sgnt in
  if s < n then begin
    let s = modulo s n in
    let m = s **% e in
    if m < pow2 (emLen * 8) then
      let em = i2osp #emLen m in
      pss_verify #msgLen sLen msg emBits em
    else false end
  else false
