module Spec.RSA

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes
open FStar.Math.Lemmas

open Spec.Bignum.Basic
open Spec.RSA.Bignum

module Hash = Spec.SHA2

val xor_bytes: #len:size_nat -> b1:lbytes len -> b2:lbytes len -> Tot (res:lbytes len)
let xor_bytes #len b1 b2 = map2 (fun x y -> logxor #U8 x y) b1 b2

val eq_bytes: #len:size_nat -> b1:lbytes len -> b2:lbytes len -> Tot bool
let eq_bytes #len b1 b2 = for_all2 (fun x y -> uint_to_nat #U8 x = uint_to_nat #U8 y) b1 b2

(* SHA256 *)
let max_input_len_sha256 = pow2 61
unfold let hLen = 32

val hash_sha256:
  #msgLen:size_nat{msgLen < max_input_len_sha256} ->
  msg:lbytes msgLen -> Tot (msgHash:lbytes hLen)
let hash_sha256 #msgLen msg = Hash.hash256 msgLen msg

(* Mask Generation Function *)
(* max_size_t = pow2 32 - 1 *)
val mgf_sha256:
  #mgfseedLen:size_nat{mgfseedLen + 4 < max_size_t /\ mgfseedLen + 4 < max_input_len_sha256} ->
  mgfseed:lbytes mgfseedLen ->
  maskLen:size_nat{0 < maskLen /\ (blocks maskLen hLen) * hLen < pow2 32} ->
  Tot (mask:lbytes maskLen)
  #reset-options "--z3rlimit 50 --max_fuel 0"
let mgf_sha256 #mgfseedLen mgfseed maskLen =
  let counter_max = blocks maskLen hLen in
  let accLen : size_nat = counter_max * hLen in
  let acc = create accLen (u8 0) in
  let mgfseed_counter = create (mgfseedLen + 4) (u8 0) in
  let mgfseed_counter = update_slice mgfseed_counter 0 mgfseedLen mgfseed in

  let acc =
    repeati counter_max
    (fun i acc ->
      let counter = nat_to_bytes_be 4 i in
      let mgfseed_counter = update_slice mgfseed_counter mgfseedLen (mgfseedLen + 4) counter in
      let mHash = hash_sha256 mgfseed_counter in
      update_slice acc (hLen * i) (hLen * i + hLen) mHash
    ) acc in
  slice acc 0 maskLen

(* RSA *)
type modBits = modBits:size_pos{64 <= modBits /\ 2 * 64 * (blocks modBits 64 + 1) < max_size_t /\
                                blocks (8 * (blocks modBits 8)) 8 < max_size_t}

noeq type rsa_pubkey (modBits:modBits) (eBits:size_pos) =
  | Mk_rsa_pubkey: n:bignum modBits{1 < bn_v n /\ pow2 (modBits - 1) <= bn_v n} ->
                   e:bignum eBits{bn_v e < bn_v n} -> rsa_pubkey modBits eBits

noeq type rsa_privkey (modBits:modBits) (eBits:size_pos) (dBits:size_pos) (pBits:size_pos) (qBits:size_pos) =
  | Mk_rsa_privkey: pkey:rsa_pubkey modBits eBits ->
		    d:bignum dBits{0 < bn_v d /\ bn_v d < bn_v (Mk_rsa_pubkey?.n pkey)} ->
		    p:bignum pBits{1 < bn_v p /\ bn_v p < bn_v (Mk_rsa_pubkey?.n pkey) /\ pBits + qBits + 64 < max_size_t /\ dBits < pBits + qBits + 64} ->
		    q:bignum qBits{1 < bn_v q /\ bn_v q < bn_v (Mk_rsa_pubkey?.n pkey) /\ bn_v (Mk_rsa_pubkey?.n pkey) = bn_v p * bn_v q}
		    -> rsa_privkey modBits eBits dBits pBits qBits

val pss_encode:
  #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256} ->
  #msgLen:size_nat{msgLen < max_input_len_sha256} ->
  salt:lbytes sLen ->
  msg:lbytes msgLen ->
  emBits:size_nat{emBits > 0 /\ hLen + sLen + 2 <= (blocks emBits 8)} -> Tot (lbytes (blocks emBits 8))

let pss_encode #sLen #msgLen salt msg emBits =
  let emLen = blocks emBits 8 in
  let msBits = emBits % 8 in

  let mHash = hash_sha256 msg in
  let m1Len = 8 + hLen + sLen in
  //m1 = [8 * 0x00; mHash; salt]
  let m1 = create m1Len (u8 0) in
  let m1 = update_slice m1 8 (8 + hLen) mHash in
  let m1 = update_slice m1 (8 + hLen) m1Len salt in
  let m1Hash = hash_sha256 m1 in

  let dbLen:size_pos = emLen - hLen - 1 in
  //db = [0x00;..; 0x00; 0x01; salt]
  let db = create dbLen (u8 0) in
  let last_before_salt = dbLen - sLen - 1 in
  let db = db.[last_before_salt] <- (u8 1) in
  let db = update_slice db (last_before_salt + 1) dbLen salt in
  let dbMask = mgf_sha256 m1Hash dbLen in
  let maskedDB = xor_bytes db dbMask in
  let maskedDB =
    if msBits > 0 then
      maskedDB.[0] <- logand #U8 maskedDB.[0] ((u8 0xff) >>. u32 (8 - msBits))
    else maskedDB in

  let em = create emLen (u8 0) in
  //em = [maskedDB; m1Hash; 0xbc]
  let em = update_slice em 0 dbLen maskedDB in
  let em = update_slice em dbLen (dbLen + hLen) m1Hash in
  em.[emLen - 1] <- (u8 0xbc)

val pss_verify:
  #msgLen:size_nat{msgLen < max_input_len_sha256} ->
  sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256} ->
  msg:lbytes msgLen ->
  emBits:size_nat{emBits > 0} ->
  em:lbytes (blocks emBits 8) -> Tot bool

let pss_verify #msgLen sLen msg emBits em =
  let emLen:size_pos = blocks emBits 8 in
  let msBits = emBits % 8 in
  let mHash = hash_sha256 msg in

  let em_0 = if msBits > 0 then em.[0] &. (u8 0xff <<. u32 msBits) else u8 0 in
  let em_last = em.[emLen - 1] in

  if (emLen < sLen + hLen + 2) then false
  else begin
    if (not (uint_to_nat #U8 em_last = 0xbc && uint_to_nat #U8 em_0 = 0)) then false
    else begin
      let dbLen:size_pos = emLen - hLen - 1 in
      let maskedDB = slice em 0 dbLen in
      let m1Hash = slice em dbLen (dbLen + hLen) in
      let dbMask = mgf_sha256 m1Hash dbLen in
      let db = xor_bytes maskedDB dbMask in
      let db =
	if msBits > 0
	then db.[0] <- logand #U8 db.[0] (u8 0xff >>. u32 (8 - msBits))
	else db in

      let padLen:size_pos = emLen - sLen - hLen - 1 in
      let pad2 = create padLen (u8 0) in
      let pad2 = pad2.[padLen - 1] <- (u8 0x01) in

      let pad = slice db 0 padLen in
      let salt = slice db padLen (padLen + sLen) in

      let m1Len = 8 + hLen + sLen in
      let m1 = create m1Len (u8 0) in
      let m1 = update_sub m1 8 hLen mHash in
      let m1 = update_sub m1 (8 + hLen) sLen salt in
      let m1Hash0 = hash_sha256 m1 in

      if not (eq_bytes pad pad2) then false
      else eq_bytes m1Hash0 m1Hash
    end
  end

val rsapss_sign:
  #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256} ->
  #msgLen:size_nat{msgLen < max_input_len_sha256} -> #eBits:size_pos ->
  modBits:modBits{sLen + hLen + 2 <= (blocks (modBits - 1) 8)} -> dBits:size_pos ->
  pBits:size_pos -> qBits:size_pos ->
  skey:rsa_privkey modBits eBits dBits pBits qBits ->
  salt:lbytes sLen -> rBlind:bignum 64 ->
  msg:lbytes msgLen -> Tot (sgnt:lbytes (blocks (8 * (blocks modBits 8)) 8))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let rsapss_sign #sLen #msgLen #eBits modBits dBits pBits qBits skey salt rBlind msg =
  let pkey = Mk_rsa_privkey?.pkey skey in
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let d = Mk_rsa_privkey?.d skey in
  let p = Mk_rsa_privkey?.p skey in
  let q = Mk_rsa_privkey?.q skey in

  let emBits = modBits - 1 in
  let em = pss_encode salt msg emBits in
  let m = bn_from_bytes_be em in
  assume (8 * blocks emBits 8 <= modBits /\ bn_v m < bn_v n); // <== fix bn_from_bytes_be
  let s = rsa_blinding modBits n pBits p qBits q m dBits d rBlind in
  bn_to_bytes_be s

val rsapss_verify:
  #msgLen:size_nat{msgLen < max_input_len_sha256} ->
  modBits:modBits -> eBits:size_pos ->
  pkey:rsa_pubkey modBits eBits ->
  sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256} ->
  msg:lbytes msgLen ->
  sgnt:lbytes (blocks modBits 8) -> Tot bool

let rsapss_verify #msgLen modBits eBits pkey sLen msg sgnt =
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let s = bn_from_bytes_be sgnt in
  assume (8 * blocks modBits 8 <= modBits); // <== fix bn_from_bytes_be

  if not (bn_is_less s n) then false
  else begin
    let m = mod_exp modBits n s eBits e in
    let emBits = modBits - 1 in
    assume (bn_v m < pow2 emBits); // <== where should we check this condition?
    let m = bn_cast_le emBits m in
    let em = bn_to_bytes_be m in
    pss_verify sLen msg emBits em
  end
