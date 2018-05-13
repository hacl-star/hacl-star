module Spec.RSAPSS

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes
open FStar.Math.Lemmas

module Hash = Spec.SHA2

#reset-options "--z3rlimit 50 --max_fuel 0"

val blocks: x:size_nat{x > 0} -> m:size_nat{m > 0} -> Tot (r:size_nat{r > 0 /\ x <= m * r})
let blocks x m = (x - 1) / m + 1

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

(* Bignum convert functions *)
val os2ip: #bLen:size_nat -> b:lbytes bLen -> Tot (res:nat{res < pow2 (8 * bLen)})
let os2ip #bLen b = nat_from_intseq_be #U8 #bLen b

val i2osp: #bLen:size_nat -> n:nat{n < pow2 (8 * bLen)} -> Tot (lbytes bLen)
let i2osp #bLen n = nat_to_bytes_be bLen n

(* Bignum library *)
type elem n = x:nat{x < n}

val mod_exp_: n:nat -> a:elem n -> b:nat -> acc:elem n -> Tot (elem n) (decreases b)
let rec mod_exp_ n a b acc =
  if b = 0
  then acc
  else begin
    let a2 = (a * a) % n in
    let acc2 = if ((b % 2) = 0) then acc else (a * acc) % n in
    mod_exp_ n a2 (b / 2) acc2 end

val mod_exp: n:nat{n > 1} -> a:elem n -> b:nat -> Tot (elem n)
let mod_exp n a b = mod_exp_ n a b 1

(* RSA *)
type modBits = modBits:size_nat{1 < modBits}

noeq type rsa_pubkey (modBits:modBits) =
  | Mk_rsa_pubkey: n:nat{1 < n /\ pow2 (modBits - 1) <= n /\ n < pow2 modBits} ->
                   e:elem n{1 < e} -> rsa_pubkey modBits

noeq type rsa_privkey (modBits:modBits) =
  | Mk_rsa_privkey: pkey:rsa_pubkey modBits ->
                    d:elem (Mk_rsa_pubkey?.n pkey){1 < d} -> rsa_privkey modBits

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
  let m1Len:size_nat = 8 + hLen + sLen in
  //m1 = [8 * 0x00; mHash; salt]
  let m1 = create m1Len (u8 0) in
  let m1 = update_slice m1 8 (8 + hLen) mHash in
  let m1 = update_slice m1 (8 + hLen) m1Len salt in
  let m1Hash = hash_sha256 #m1Len m1 in

  let dbLen:size_nat = emLen - hLen - 1 in
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
  let (emLen:size_nat{emLen > 0}) = blocks emBits 8 in
  let msBits = emBits % 8 in
  let mHash = hash_sha256 msg in

  let em_0 = if msBits > 0 then em.[0] &. (u8 0xff <<. u32 msBits) else u8 0 in
  let em_last = em.[emLen - 1] in
  
  if (emLen < sLen + hLen + 2) then false
  else begin
    if (not (uint_to_nat #U8 em_last = 0xbc && uint_to_nat #U8 em_0 = 0)) then false
    else begin
      let (dbLen:size_nat{dbLen > 0}) = emLen - hLen - 1 in
      let maskedDB = slice em 0 dbLen in
      let m1Hash = slice em dbLen (dbLen + hLen) in
      
      let dbMask = mgf_sha256 m1Hash dbLen in
      let db = xor_bytes maskedDB dbMask in
      let db =
	if msBits > 0
	then db.[0] <- logand #U8 db.[0] (u8 0xff >>. u32 (8 - msBits))
	else db in

      let (padLen:size_nat{padLen > 0}) = emLen - sLen - hLen - 1 in
      let pad2 = create padLen (u8 0) in
      let pad2 = pad2.[padLen - 1] <- (u8 0x01) in

      let pad = slice db 0 padLen in
      let salt = slice db padLen (padLen + sLen) in

      if not (eq_bytes pad pad2) then false
      else begin
	let m1Len:size_nat = 8 + hLen + sLen in
	let m1 = create m1Len (u8 0) in
	let m1 = update_slice m1 8 (8 + hLen) mHash in
	let m1 = update_slice m1 (8 + hLen) m1Len salt in
	let m1Hash0 = hash_sha256 #m1Len m1 in
	eq_bytes m1Hash0 m1Hash
      end
    end
  end

val rsapss_sign:
  #sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256} ->
  #msgLen:size_nat{msgLen < max_input_len_sha256} ->
  modBits:modBits{sLen + hLen + 2 <= (blocks (modBits - 1) 8)} ->
  skey:rsa_privkey modBits ->
  salt:lbytes sLen ->
  msg:lbytes msgLen -> Tot (sgnt:lbytes (blocks modBits 8))

let rsapss_sign #sLen #msgLen modBits skey salt msg =
  let pkey = Mk_rsa_privkey?.pkey skey in
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let d = Mk_rsa_privkey?.d skey in

  let nLen = blocks modBits 8 in
  assert (modBits <= 8 * nLen);
  pow2_le_compat (8 * nLen) modBits;
  assert (pow2 modBits <= pow2 (8 * nLen));
  assert (n < pow2 (8 * nLen));

  let emBits = modBits - 1 in
  let em = pss_encode #sLen #msgLen salt msg emBits in
  let emLen = blocks emBits 8 in
  let m = os2ip #emLen em in
  assume (m < n);
  let s = mod_exp n m d in
  assert (s < n);
  i2osp #nLen s

val rsapss_verify:
  #msgLen:size_nat{msgLen < max_input_len_sha256} ->
  modBits:modBits ->
  pkey:rsa_pubkey modBits ->
  sLen:size_nat{sLen + hLen + 8 < max_size_t /\ sLen + hLen + 8 < max_input_len_sha256} ->
  msg:lbytes msgLen ->
  sgnt:lbytes (blocks modBits 8) -> Tot bool

let rsapss_verify #msgLen modBits pkey sLen msg sgnt =
  let n = Mk_rsa_pubkey?.n pkey in
  let e = Mk_rsa_pubkey?.e pkey in
  let nLen = blocks modBits 8 in
  assert (modBits <= 8 * nLen);
  pow2_le_compat (8 * nLen) modBits;
  assert (pow2 modBits <= pow2 (8 * nLen));
  assert (n < pow2 (8 * nLen));

  let s = os2ip #nLen sgnt in
  if s < n then begin
    let m = mod_exp n s e in
    let emBits = modBits - 1 in
    let emLen = blocks emBits 8 in
    assume (m < pow2 (emLen * 8));
    let em = i2osp #emLen m in
    pss_verify #msgLen sLen msg emBits em end
  else false
