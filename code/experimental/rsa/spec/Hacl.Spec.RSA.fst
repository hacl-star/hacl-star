module Hacl.Spec.RSA

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Spec.Lib.Loops
open Spec.Lib.RawIntTypes

open Hacl.Spec.Lib
open Hacl.Spec.MGF
open Hacl.Spec.Comparison
open Hacl.Spec.Convert
open Hacl.Spec.Exponentiation
open Hacl.Spec.Addition
open Hacl.Spec.Multiplication

val xor_bytes: len:size_nat -> b1:lbytes len -> b2:lbytes len -> Tot (b1:lbytes len)
let xor_bytes len b1 b2 = map2 (fun x y -> logxor #U8 x y) b1 b2

val eq_bytes: len:size_nat -> b1:lbytes len -> b2:lbytes len -> Tot bool
let eq_bytes len b1 b2 = for_all2 (fun x y -> uint_to_nat #U8 x = uint_to_nat #U8 y) b1 b2

val pss_encode_:
  sLen:size_nat{sLen + hLen + 8 < max_size_t} -> salt:lbytes sLen ->
  msgLen:size_nat{msgLen < max_input_len_sha256} -> msg:lbytes msgLen ->
  emLen:size_nat{emLen - sLen - hLen - 2 >= 0} -> em:lbytes emLen -> Tot (em:lbytes emLen)
  #reset-options "--z3rlimit 50 --max_fuel 0"
let pss_encode_ sLen salt msgLen msg emLen em =
  let m1_size:size_nat = 8 + hLen + sLen in
  assert_norm (m1_size < max_input_len_sha256);
  let db_size:size_nat = emLen - hLen - 1 in
    
  assume (sLen + hLen + 8 + 2 * emLen < max_size_t);
  assume (4 + 2 * hLen + hLen * (blocks db_size hLen) < max_size_t);
  let stLen:size_nat = hLen + m1_size + hLen + db_size + db_size in
  let st = create stLen (u8 0) in
  
  let mHash = sub st 0 hLen in
  let m1 = sub st hLen m1_size in
  let m1Hash = sub st (hLen + m1_size) hLen in
  let db = sub st (hLen + m1_size + hLen) db_size in
  let dbMask = sub st (hLen + m1_size + hLen + db_size) db_size in
  
  let mHash = hash_sha256 msgLen msg mHash in
  let m1 = update_sub m1 8 hLen mHash in
  let m1 = update_sub m1 (8 + hLen) sLen salt in
  let m1Hash = hash_sha256 m1_size m1 m1Hash in
       
  let last_before_salt = db_size - sLen - 1 in
  let db = db.[last_before_salt] <- u8 1 in
  let db = update_sub db (last_before_salt + 1) sLen salt in
  let dbMask = mgf_sha256 m1Hash db_size dbMask in
  let db = xor_bytes db_size db dbMask in

  let em = update_sub em 0 db_size db in
  let em = update_sub em db_size hLen m1Hash in
  let em = em.[emLen - 1] <- u8 0xbc in em

val pss_encode:
  msBits:size_nat{msBits < 8} ->
  sLen:size_nat{sLen + hLen + 8 < max_size_t} -> salt:lbytes sLen ->
  msgLen:size_nat{msgLen < max_input_len_sha256} -> msg:lbytes msgLen ->
  emLen:size_nat{emLen - sLen - hLen - 3 >= 0} ->
  em:lbytes emLen -> Tot (em:lbytes emLen)
let pss_encode msBits sLen salt msgLen msg emLen em =
  if (msBits = 0)
  then begin
    let em' = sub em 1 (emLen - 1) in
    let em' = pss_encode_ sLen salt msgLen msg (emLen - 1) em' in 
    update_sub em 1 (emLen - 1) em' end
  else begin
    let em = pss_encode_ sLen salt msgLen msg emLen em in
    let shift' = 8 - msBits in
    em.[0] <- em.[0] &.(u8 0xff >>. u32 shift')
  end

val pss_verify_:
  sLen:size_nat{sLen + hLen + 8 < max_size_t} ->
  msBits:size_nat{msBits < 8} ->
  emLen:size_nat{emLen - sLen - hLen - 2 >= 0} -> em:lbytes emLen ->
  msgLen:size_nat{msgLen < max_input_len_sha256} -> msg:lbytes msgLen -> Tot bool
  #reset-options "--z3rlimit 50 --max_fuel 0"
let pss_verify_ sLen msBits emLen em msgLen msg =
  let pad_size:size_nat = emLen - sLen - hLen - 1 in
  let (db_size:size_nat{db_size > 0}) = emLen - hLen - 1 in
  assert_norm (db_size < max_input_len_sha256);
  let m1_size:size_nat = 8 + hLen + sLen in
  assert_norm (m1_size < max_input_len_sha256);
  
  assume (2 * emLen +  8 + hLen  < max_size_t);
  assume (4 + 2 * hLen + hLen * (blocks db_size hLen) < max_size_t);
  let stLen:size_nat = hLen + pad_size + db_size + m1_size + hLen in
  let st = create stLen (u8 0) in
  
  let mHash = sub st 0 hLen in
  let pad2 = sub st hLen pad_size in
  let dbMask = sub st (hLen + pad_size) db_size in
  let m1 = sub st (hLen + pad_size + db_size) m1_size in
  let m1Hash' = sub st (hLen + pad_size + db_size + m1_size) hLen in
       
  let mHash = hash_sha256 msgLen msg mHash in
  let pad2 = pad2.[pad_size - 1] <- u8 0x01 in
  let maskedDB = sub em 0 db_size in
  let m1Hash = sub em db_size hLen in
  let dbMask = mgf_sha256 m1Hash db_size dbMask in
  let dbMask = xor_bytes db_size dbMask maskedDB in
  let dbMask =
    if (msBits > 0) then begin
      let shift' = 8 - msBits in
      dbMask.[0] <- dbMask.[0] &. (u8 0xff >>. u32 shift') end
    else dbMask in

  let pad = sub dbMask 0 pad_size in
  let salt = sub dbMask pad_size sLen in
  
  let res =
    if not (eq_bytes pad_size pad pad2) then false
    else begin
      let m1 = update_sub m1 8 hLen mHash in
      let m1 = update_sub m1 (8 + hLen) sLen salt in
      let m1Hash' = hash_sha256 m1_size m1 m1Hash' in
      eq_bytes hLen m1Hash m1Hash'
    end in
  res

val pss_verify:
  sLen:size_nat{sLen + hLen + 8 < max_size_t} ->
  msBits:size_nat{msBits < 8} ->
  emLen:size_nat{emLen - sLen - hLen - 2 >= 0} -> em:lbytes emLen ->
  msgLen:size_nat{msgLen < max_input_len_sha256} -> msg:lbytes msgLen -> Tot bool
let pss_verify sLen msBits emLen em msgLen msg =
  let em_0 = em.[0] &. (u8 0xff <<. u32 msBits) in
  let em_last = em.[emLen - 1] in

  if not ((eq_u8 em_0 (u8 0)) && (eq_u8 em_last (u8 0xbc)))
  then false
  else begin
    let emLen1 = if msBits = 0 then emLen - 1 else emLen in
    let em1:lbytes emLen1 = if msBits = 0 then sub em 1 emLen1 else em in
    if (emLen1 < sLen + hLen + 2) then false
    else pss_verify_ sLen msBits emLen1 em1 msgLen msg
  end

val rsa_sign:
  nLen:size_nat{0 < nLen /\ 128 * (nLen + 1) < max_size_t} ->
  pow2_i:size_nat{9 * (1 + nLen) + 4 * pow2_i < max_size_t /\ (1 + nLen) < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + (1 + nLen) = pow2_i} ->
  modBits:size_nat{0 < modBits /\ nLen = bits_to_bn modBits} ->
  eBits:size_nat{0 < eBits /\ eBits <= modBits} ->
  dBits:size_nat{0 < dBits /\ dBits <= modBits} ->
  pLen:size_nat{0 < pLen} -> qLen:size_nat{0 < qLen /\ nLen + (bits_to_bn eBits) + (bits_to_bn dBits) + pLen + qLen < max_size_t} ->
  skey:lseqbn (nLen + (bits_to_bn eBits) + (bits_to_bn dBits) + pLen + qLen) ->
  rBlind:uint64 ->
  sLen:size_nat{sLen + hLen + 8 < max_size_t /\ (blocks modBits 8) - sLen - hLen - 3 >= 0} -> salt:lbytes sLen ->
  msgLen:size_nat{msgLen < max_input_len_sha256} -> msg:lbytes msgLen ->
  sgnt:lbytes (blocks modBits 8) -> Tot (lbytes (blocks modBits 8))
  #reset-options "--z3rlimit 150 --max_fuel 0"
let rsa_sign nLen pow2_i iLen modBits eBits dBits pLen qLen skey rBlind sLen salt msgLen msg sgnt =
  let k = blocks modBits 8 in
  let msBits = (modBits - 1) % 8 in

  //let nLen = bits_to_bn modBits in
  let nLen = get_size_nat k in
  let eLen = bits_to_bn eBits in
  let dLen = bits_to_bn dBits in
  let skeyLen:size_nat = nLen + eLen + dLen + pLen + qLen in
    
  let n = sub skey 0 nLen in
  let e = sub skey nLen eLen in
  let d = sub skey (nLen + eLen) dLen in
  let p = sub skey (nLen + eLen + dLen) pLen in
  let q = sub skey (nLen + eLen + dLen + pLen) qLen in
    
  assume (2 * nLen + 2 * (pLen + qLen) + 1 < max_size_t);
  let n2Len = nLen + nLen in
  let pqLen = pLen + qLen in
  let stLen:size_nat = n2Len + pqLen + pqLen + 1 in
  let em = create k (u8 0) in
  let em = pss_encode msBits sLen salt msgLen msg k em in

  let tmp = create stLen (u64 0) in
    
  let m = sub tmp 0 nLen in
  let s = sub tmp nLen nLen in
  let phi_n = sub tmp n2Len pqLen in
  let p1 = sub tmp (n2Len + pqLen) pLen in
  let q1 = sub tmp (n2Len + pqLen + pLen) qLen in
  let dLen':size_nat  = pLen + qLen + 1 in
  let d' = sub tmp (n2Len + pqLen) dLen' in
  let m = text_to_nat k em m in

  let p1 = bn_sub_u64 pLen p (u64 1) p1 in // p1 = p - 1
  let q1 = bn_sub_u64 qLen q (u64 1) q1 in // q1 = q - 1
  let phi_n = bn_mul pLen p1 qLen q1 phi_n in // phi_n = p1 * q1
  let d' = bn_mul_u64 pqLen phi_n rBlind d' in //d' = phi_n * rBlind
  assume (dLen <= dLen' /\ dLen' * 64 < max_size_t);
  let d' = bn_add dLen' d' dLen d d' in //d' = d' + d
  assume (nLen = bits_to_bn modBits);
  let s = mod_exp nLen pow2_i iLen modBits n m (dLen' * 64) d' s in
  nat_to_text k s sgnt

val rsa_verify:
  nLen:size_nat{0 < nLen /\ 128 * (nLen + 1) < max_size_t} ->
  pow2_i:size_nat{9 * (1 + nLen) + 4 * pow2_i < max_size_t /\ (1 + nLen) < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + (1 + nLen) = pow2_i} ->
  modBits:size_nat{0 < modBits /\ nLen = bits_to_bn modBits} ->
  eBits:size_nat{0 < eBits /\ eBits <= modBits /\ nLen + (bits_to_bn eBits) < max_size_t} ->
  pkey:lseqbn (nLen + (bits_to_bn eBits)) ->
  sLen:size_nat{sLen + hLen + 8 < max_size_t /\ (blocks modBits 8) - sLen - hLen - 3 >= 0} ->
  sgnt:lbytes (blocks modBits 8) ->
  msgLen:size_nat{msgLen < max_input_len_sha256} -> msg:lbytes msgLen -> Tot bool
  #reset-options "--z3rlimit 150 --max_fuel 0"
let rsa_verify nLen pow2_i iLen modBits eBits pkey sLen sgnt msgLen msg =
  let k = blocks modBits 8 in
  let msBits = (modBits - 1) % 8 in
  //let nLen = bits_to_bn modBits in
  let nLen = get_size_nat k in
  let eLen = bits_to_bn eBits in
  let pkeyLen:size_nat = nLen + eLen in
  
  let n = sub pkey 0 nLen in
  let e = sub pkey nLen eLen in
  
  let n2Len:size_nat = nLen + nLen in
  let tmp = create n2Len (u64 0) in
  let s = sub tmp nLen nLen in
  let s = text_to_nat k sgnt s in
  let tmp = update_sub tmp nLen nLen s in
  let m = sub tmp 0 nLen in
  let s = sub tmp nLen nLen in
  let em = create k (u8 0) in

  if (bn_is_less nLen s nLen n) then begin
    let m = mod_exp nLen pow2_i iLen modBits n s eBits e m in
    let em = nat_to_text k m em in
    pss_verify sLen msBits k em msgLen msg end
  else false
