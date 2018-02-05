module Spec.RSA

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes

open FStar.Math.Lemmas
open Spec.RSA.Lemmas
open Spec.RSA.Bignum

module Hash = Spec.SHA2

#reset-options "--z3rlimit 50 --max_fuel 0"

val blocks: x:size_nat{x > 0} -> m:size_nat{m > 0} -> Tot (r:size_nat{r > 0 /\ x <= m * r})
let blocks x m = (x - 1) / m + 1

val xor_bytes: len:size_nat -> b1:lbytes len -> b2:lbytes len -> Tot (res:lbytes len)
let xor_bytes len b1 b2 = map2 (fun x y -> x ^. y) b1 b2

val eq_bytes: len:size_nat -> b1:lbytes len -> b2:lbytes len -> Tot bool
let eq_bytes len b1 b2 = for_all2 (fun x y -> uint_to_nat #U8 x = uint_to_nat #U8 y) b1 b2

(* SHA256 *)
let max_input_len_sha256 = pow2 61
unfold let hLen = 32
val hash_sha256:
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen ->
    hash:lbytes hLen ->
    Tot (msgHash:lbytes hLen)
let hash_sha256 msgLen msg hash = Hash.hash256 msgLen msg

(* Mask Generation Function *)
val mgf_sha256_loop:
    mgfseedLen:size_nat{mgfseedLen = hLen + 4 /\ mgfseedLen < max_input_len_sha256} ->
    mgfseed:lbytes mgfseedLen ->
    counter_max:size_nat{counter_max * hLen < pow2 32}->
    accLen:size_nat{accLen = counter_max * hLen} ->
    acc:lbytes accLen ->
    Tot (res:lbytes accLen)

#reset-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

let mgf_sha256_loop mgfseedLen mgfseed counter_max accLen acc =
    let mHash = create hLen (u8 0) in
    let next (i:size_nat{i < counter_max}) (acc:lbytes accLen) : lbytes accLen =
        let counter = nat_to_bytes_be 4 i in
        let mgfseed = update_sub mgfseed hLen 4 counter in
        let mHash = hash_sha256 mgfseedLen mgfseed mHash in
        update_sub acc (hLen * i) hLen mHash in
    repeati #(lbytes accLen) counter_max next acc

(* We only allow U32.t masklen, this means that we always have the property
   that maskLen <= op_Multiply (pow2 32) (U32.v hLen) as required by the spec *)
val mgf_sha256:
    mgfseedLen:size_nat{mgfseedLen = hLen + 4 /\ mgfseedLen < max_input_len_sha256} ->
    mgfseed:lbytes mgfseedLen ->
    maskLen:size_nat{maskLen > 0 /\ (blocks maskLen hLen) * hLen < pow2 32} ->
    mask:lbytes maskLen ->
    Tot (mask':lbytes maskLen)

#reset-options "--z3rlimit 50 --max_fuel 0"

let mgf_sha256 mgfseedLen mgfseed maskLen mask =
    let counter_max = blocks maskLen hLen in
    let accLen : size_nat = counter_max * hLen in
    let acc = create accLen (u8 0) in
    let acc = mgf_sha256_loop mgfseedLen mgfseed counter_max accLen acc in
    slice acc 0 maskLen

(* RSA *)
type modBits = modBits:size_nat{1 < modBits /\ modBits + 3 < pow2 32}

noeq type rsa_pubkey (modBits:modBits) =
     | Mk_rsa_pubkey: n:bignum{1 < n /\ pow2 (modBits - 1) <= n /\ n < pow2 modBits} ->
                      e:elem n{1 < e} -> rsa_pubkey modBits
	
noeq type rsa_privkey (modBits:modBits) =
     | Mk_rsa_privkey: pkey:rsa_pubkey modBits ->
                       d:elem (Mk_rsa_pubkey?.n pkey){1 < d} ->
                       p:elem (Mk_rsa_pubkey?.n pkey){1 < p} ->
                       q:elem (Mk_rsa_pubkey?.n pkey){1 < q /\ (Mk_rsa_pubkey?.n pkey) = p * q} -> rsa_privkey modBits

val pss_encode_:
    sLen:size_nat{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
    salt:lbytes sLen ->
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen ->
    emLen:size_nat{0 <= emLen - sLen - hLen - 2 /\ emLen < pow2 32} ->
    em:lbytes emLen ->
    Tot (em':lbytes emLen)

let pss_encode_ sLen salt msgLen msg emLen em =
    let mHash = create hLen (u8 0) in
    let mHash = hash_sha256 msgLen msg mHash in

    //m1 = [8 * 0x00; mHash; salt]
    let m1_size : size_nat = 8 + hLen + sLen in
    let m1 = create m1_size (u8 0) in
    let m1 = update_sub m1 8 hLen mHash in
    let m1 = update_sub m1 (8 + hLen) sLen salt in
    let m1Hash = create 36 (u8 0) in
    let m1Hash' = sub m1Hash 0 hLen in
    let m1Hash' = hash_sha256 m1_size m1 m1Hash' in
    let m1Hash = update_sub m1Hash 0 hLen m1Hash' in

    //db = [0x00; ..; 0x00; 0x01; salt]
    let db_size : size_nat = emLen - hLen - 1 in
    let db = create db_size (u8 0) in
    let last_before_salt = db_size - sLen - 1 in
    let db = db.[last_before_salt] <- (u8 1) in
    let db = update_sub db (last_before_salt + 1) sLen salt in

    let dbMask = create db_size (u8 0) in
    let dbMask = mgf_sha256 (hLen + 4) m1Hash db_size dbMask in
    let maskedDB = xor_bytes db_size db dbMask in
    //em = [maskedDB; m1Hash'; 0xbc]
    let em = update_sub em 0 db_size maskedDB in
    let em = update_sub em db_size hLen m1Hash' in
    em.[emLen - 1] <- (u8 0xbc)

val pss_encode:
    msBits:size_nat{msBits < 8} ->
    sLen:size_nat{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
    salt:lbytes sLen ->
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen ->
    emLen:size_nat{0 <= emLen - sLen - hLen - 3 /\ emLen < pow2 32} ->
    em:lbytes emLen ->
    Tot (lbytes emLen)

let pss_encode msBits sLen salt msgLen msg emLen em =
    if msBits = 0
    then begin
        let em' = sub em 1 (emLen - 1) in
        let em' = pss_encode_ sLen salt msgLen msg (emLen - 1) em' in
        update_sub em 1 (emLen - 1) em' end
    else begin
        let em = pss_encode_ sLen salt msgLen msg emLen em in
        assert (0 < 8 - msBits /\ 8 - msBits < 8);
        em.[0] <- em.[0] &. ((u8 0xff) >>. u32 (8 - msBits)) end

val pss_verify_:
    sLen:size_nat{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
    msBits:size_nat{msBits < 8} ->
    emLen:size_nat{0 <= emLen - sLen - hLen - 2 /\ emLen < pow2 32} ->
    em:lbytes emLen ->
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen -> Tot bool

let pss_verify_ sLen msBits emLen em msgLen msg =
    let mHash = create hLen (u8 0) in
    let mHash = hash_sha256 msgLen msg mHash in

    let (pad_size:size_nat{pad_size > 0}) = emLen - sLen - hLen - 1 in
    let pad2 = create pad_size (u8 0) in
    let pad2 = pad2.[pad_size - 1] <- (u8 0x01) in

    let (db_size:size_nat{db_size > 0}) = emLen - hLen - 1 in
    let maskedDB = slice em 0 db_size in
    let m1Hash0 = slice em db_size (db_size + hLen) in
    let m1Hash = create 36 (u8 0) in
    let m1Hash = update_sub m1Hash 0 hLen m1Hash0 in
    let dbMask = create db_size (u8 0) in
    let dbMask = mgf_sha256 (hLen + 4) m1Hash db_size dbMask in
    let db = xor_bytes db_size maskedDB dbMask in
    let db =
        if msBits > 0
        then begin
            assert (0 < 8 - msBits /\ 8 - msBits < 8);
            db.[0] <- db.[0] &. (u8 0xff >>. u32 (8 - msBits)) end
        else db in
	
    let pad = slice db 0 pad_size in
    let salt = slice db pad_size (pad_size + sLen) in

    let m1_size:size_nat = 8 + hLen + sLen in
    let m1 = create m1_size (u8 0) in
    let m1Hash' = create hLen (u8 0) in
    if not (eq_bytes pad_size pad pad2) then false
    else begin
        (* first 8 elements should be 0x00 *)
        let m1 = update_sub m1 8 hLen mHash in
        let m1 = update_sub m1 (8 + hLen) sLen salt in
        let m1Hash' = hash_sha256 m1_size m1 m1Hash' in
        eq_bytes hLen m1Hash0 m1Hash'
    end

val pss_verify:
    sLen:size_nat{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
    msBits:size_nat{msBits < 8} ->
    emLen:size_nat{0 < emLen /\ emLen < pow2 32} ->
    em:lbytes emLen ->
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen -> Tot bool

let pss_verify sLen msBits emLen em msgLen msg =
    let em_0 = em.[0] &. (u8 0xff <<. u32 msBits) in
    let em_last = em.[emLen - 1] in

    if not ((uint_to_nat #U8 em_0 = 0) && (uint_to_nat #U8 em_last = 0xbc))
    then false
    else begin
        let emLen' = if msBits = 0 then emLen - 1 else emLen in
        let em':lbytes emLen' = if msBits = 0 then sub em 1 (emLen - 1) else em in
        if (emLen' < sLen + hLen + 2)
        then false
        else pss_verify_ sLen msBits emLen' em' msgLen msg
    end

val rsa_sign:
    x0:size_nat ->
    modBits:modBits{pow2 (modBits + 2) < pow2 (pow2 x0)} ->
    skey:rsa_privkey modBits ->
    rBlind:bignum{rBlind < pow2 64} ->
    sLen:size_nat{sLen + hLen + 8 < pow2 32 /\ 0 <= (blocks modBits 8) - sLen - hLen - 3 /\
                  sLen + hLen + 8 < max_input_len_sha256} ->
    salt:lbytes sLen ->
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen ->
    Tot (sgnt:lbytes (blocks modBits 8))

let rsa_sign x0 modBits skey rBlind sLen salt msgLen msg =
    let pkey = Mk_rsa_privkey?.pkey skey in
    let n = Mk_rsa_pubkey?.n pkey in
    let e = Mk_rsa_pubkey?.e pkey in
    let d = Mk_rsa_privkey?.d skey in
    let p = Mk_rsa_privkey?.p skey in
    let q = Mk_rsa_privkey?.q skey in
    let k = blocks modBits 8 in
    assert (modBits <= 8 * k);
    pow2_le_compat (8 * k) modBits;
    assert (pow2 modBits <= pow2 (8 * k));
    assert (n < pow2 (8 * k));
	
    let msBits = (modBits - 1) % 8 in
    let em = create k (u8 0) in
    let em = pss_encode msBits sLen salt msgLen msg k em in
    let m = os2ip k em in
	
    assume (m < n);
    let s = rsa_blinding x0 modBits n p q d m rBlind in

    let sgnt = create k (u8 0) in
    assert (s < n);
    i2osp s k sgnt

val rsa_verify:
    x0:size_nat ->
    modBits:modBits{pow2 (modBits + 2) < pow2 (pow2 x0)} ->
    pkey:rsa_pubkey modBits ->
    sLen:size_nat{sLen + hLen + 8 < pow2 32 /\ sLen + hLen + 8 < max_input_len_sha256} ->
    sgnt:lbytes (blocks modBits 8) ->
    msgLen:size_nat{msgLen < max_input_len_sha256} ->
    msg:lbytes msgLen -> Tot bool

let rsa_verify x0 modBits pkey sLen sgnt msgLen msg =
    let n = Mk_rsa_pubkey?.n pkey in
    let e = Mk_rsa_pubkey?.e pkey in
    let k = blocks modBits 8 in
    assert (modBits <= 8 * k);
    pow2_le_compat (8 * k) modBits;
    assert (pow2 modBits <= pow2 (8 * k));
    assert (n < pow2 (8 * k));

    let s = os2ip k sgnt in
    if bn_is_less s n then begin
        assert (s < n);
        let m = mod_exp x0 modBits n s e in
        let em = create k (u8 0) in
        let em = i2osp m k em in
        let msBits = (modBits - 1) % 8 in
        pss_verify sLen msBits k em msgLen msg end
    else false
