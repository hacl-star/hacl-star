module Hacl.Spec.RSA

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Exponentiation

module S = Spec.RSA
module BB = Hacl.Spec.Bignum.Base
module SM = Hacl.Spec.Bignum.Montgomery
module BSeq = Lib.ByteSequence

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val blocks_bits_lemma: t:limb_t -> bs:size_pos ->
  Lemma (blocks (blocks bs 8) (numbytes t) == blocks bs (bits t))
let blocks_bits_lemma t bs = ()


val blocks_numb_lemma: t:limb_t -> bs:size_pos ->
  Lemma (numbytes t * blocks (blocks bs 8) (numbytes t) <= max_size_t)
let blocks_numb_lemma t bs = ()



val bn_lt_pow2: #t:limb_t -> modBits:size_pos{1 < modBits} -> m:lbignum t (blocks modBits (bits t)) -> bool
let bn_lt_pow2 #t modBits m =
  if (modBits - 1) % 8 <> 0 then true
  else BB.unsafe_bool_of_limb0 (bn_get_ith_bit m (modBits - 1))


val bn_eval_lt_pow2_modBits:
    #t:limb_t
  -> modBits:size_pos{1 < modBits}
  -> m:lbignum t (blocks modBits (bits t)) -> Lemma
  (requires bn_v m < pow2 modBits)
  (ensures  bn_v m == (bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1))

let bn_eval_lt_pow2_modBits #t modBits m =
  calc (==) {
    bn_v m;
    (==) { Math.Lemmas.euclidean_division_definition (bn_v m) (pow2 (modBits - 1)) }
    bn_v m / pow2 (modBits - 1) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    (==) { Math.Lemmas.euclidean_division_definition (bn_v m / pow2 (modBits - 1)) 2 }
    (bn_v m / pow2 (modBits - 1) / 2 * 2 + bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v m) (pow2 (modBits - 1)) 2; Math.Lemmas.pow2_plus (modBits - 1) 1}
    (bn_v m / pow2 modBits * 2 + bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    (==) { Math.Lemmas.small_division_lemma_1 (bn_v m) (pow2 modBits) }
    (bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    }


val bn_lt_pow2_lemma: #t:limb_t -> modBits:size_pos{1 < modBits} -> m:lbignum t (blocks modBits (bits t)) -> Lemma
  (requires bn_v m < pow2 modBits)
  (ensures  bn_lt_pow2 modBits m == (bn_v m < pow2 (8 * blocks (modBits - 1) 8)))

let bn_lt_pow2_lemma #t modBits m =
  let k = blocks modBits 8 in
  let emLen = blocks (modBits - 1) 8 in
  let nLen = blocks k (numbytes t) in
  assert (nLen == blocks modBits (bits t));

  if (modBits - 1) % 8 <> 0 then Math.Lemmas.pow2_le_compat (8 * emLen) modBits
  else begin
    assert (k == emLen + 1);
    bn_eval_unfold_i m nLen;
    assert (8 * k == modBits + 7);
    assert (8 * emLen == modBits - 1);

    bn_eval_lt_pow2_modBits modBits m;
    bn_get_ith_bit_lemma m (modBits - 1) end


val bn_eval_sub: #t:limb_t -> modBits:size_pos{1 < modBits} -> m:lbignum t (blocks modBits (bits t)) -> Lemma
  (requires bn_v m < pow2 (8 * blocks (modBits - 1) 8))
  (ensures  bn_v m == bn_v (sub m 0 (blocks (blocks (modBits - 1) 8) (numbytes t))))

let bn_eval_sub #t modBits m =
  let emLen = blocks (modBits - 1) 8 in
  let mLen = blocks emLen (numbytes t) in
  let nLen = blocks modBits (bits t) in
  assert (bn_v m < pow2 (8 * emLen));
  let m1 = sub m 0 mLen in
  bn_eval_split_i m mLen;
  assert (bn_v m == bn_v m1 + pow2 (bits t * mLen) * bn_v (slice m mLen nLen));
  bn_eval_bound m1 mLen;
  assert (bn_v m1 < pow2 (bits t * mLen));
  Math.Lemmas.pow2_le_compat (bits t * mLen) (8 * emLen)


let pkey_len_pre (t:limb_t) (modBits:size_nat) (eBits:size_nat) =
  let bits = bits t in
  1 < modBits /\ 0 < eBits /\
  2 * bits * blocks modBits bits <= max_size_t /\
  bits * blocks eBits bits <= max_size_t /\
  2 * blocks modBits bits + blocks eBits bits <= max_size_t


let skey_len_pre (t:limb_t) (modBits:size_nat) (eBits:size_nat) (dBits:size_nat) =
  let bits = bits t in
  pkey_len_pre t modBits eBits /\
  0 < dBits /\ bits * blocks dBits bits <= max_size_t /\
  2 * blocks modBits bits + blocks eBits bits + blocks dBits bits <= max_size_t


val rsa_pkey_pre:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t)) -> Type0

let rsa_pkey_pre #t modBits eBits pkey =
  let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e = sub pkey (nLen + nLen) eLen in
  r2 == SM.bn_precomp_r2_mod_n (modBits - 1) n /\
  bn_v n % 2 = 1 /\
  pow2 (modBits - 1) < bn_v n /\ bn_v n < pow2 modBits /\
  0 < bn_v e /\ bn_v e < pow2 eBits


val rsa_skey_pre:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t)) -> Type0

let rsa_skey_pre #t modBits eBits dBits skey =
  let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in
  let pkeyLen = nLen + nLen + eLen in

  let pkey = sub skey 0 pkeyLen in
  let d    = sub skey pkeyLen dLen in
  rsa_pkey_pre modBits eBits pkey /\
  0 < bn_v d /\ bn_v d < pow2 dBits


val rsa_dec_post:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> cipher:lseq uint8 (blocks modBits 8)
  -> eq_m:bool
  -> msg:lseq uint8 (blocks modBits 8) -> Type0

let rsa_dec_post #t modBits eBits dBits skey cipher valid msg =
  rsa_skey_pre modBits eBits dBits skey /\
 (let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n = bn_v (sub skey 0 nLen) in
  let e = bn_v (sub skey (nLen + nLen) eLen) in
  let d = bn_v (sub skey (nLen + nLen + eLen) dLen) in
  let pkeys : S.rsa_pkey modBits = S.Mk_rsa_pkey n e in
  let skeys : S.rsa_skey modBits = S.Mk_rsa_skey pkeys d in
  let valid_s, msg_s = S.rsa_dec_skey modBits skeys cipher in
  valid == valid_s /\ msg == msg_s)

val rsa_enc_post:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> msg:lseq uint8 (blocks modBits 8)
  -> valid:bool
  -> cipher:lseq uint8 (blocks modBits 8) -> Type0

let rsa_enc_post #t modBits eBits pkey msg valid cipher =
  rsa_pkey_pre modBits eBits pkey /\
 (let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n = bn_v (sub pkey 0 nLen) in
  let e = bn_v (sub pkey (nLen + nLen) eLen) in
  let pkeys : S.rsa_pkey modBits = S.Mk_rsa_pkey n e in
  let (valid_s,cipher_s) = S.rsa_enc_pkey modBits pkeys msg in
  valid == valid_s /\ cipher == cipher_s)

val rsa_dec_bn:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> c:lbignum t (blocks modBits (bits t)) ->
  Pure (tuple2 bool (lbignum t (blocks modBits (bits t))))
  (requires
   (let nLen = blocks modBits (bits t) in
    let n  = sub skey 0 nLen in
    rsa_skey_pre modBits eBits dBits skey))
  (ensures fun res -> True)

let rsa_dec_bn #t modBits eBits dBits skey c =
  let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n  = sub skey 0 nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  let m_zero = bn_from_uint #t nLen (uint 0) in
  let lt_c = bn_lt_mask c n in
  bn_lt_mask_lemma c n;
  if BB.unsafe_bool_of_limb lt_c then begin
    let k = blocks modBits 8 in
    Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
    SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;
    let s = bn_mod_exp_consttime_precompr2 nLen n r2 c dBits d in
    let c' = bn_mod_exp_vartime_precompr2 nLen n r2 s eBits e in
    let eq_c = bn_eq_mask c c' in
    let s = map (logand eq_c) s in
    BB.unsafe_bool_of_limb eq_c, s
  end else
    false, m_zero

val rsa_dec_:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> cipher:lseq uint8 (blocks modBits 8) ->
  Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires
   (let nLen = blocks modBits (bits t) in
    let n  = sub skey 0 nLen in
    rsa_skey_pre modBits eBits dBits skey))
  (ensures fun res -> True)

let rsa_dec_ #t modBits eBits dBits skey cipher =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let cLen = blocks modBits 8 in
  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks cLen numb == blocks modBits bits);
  assert (numb * blocks cLen numb <= max_size_t);

  let c = bn_from_bytes_be #t cLen cipher in
  bn_from_bytes_be_lemma #t cLen cipher;

  let eq_b, m = rsa_dec_bn #t modBits eBits dBits skey c in
  let msg = bn_to_bytes_be cLen m in
  eq_b, msg

val rsa_dec_lemma:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> cipher:lseq uint8 (blocks modBits 8) -> Lemma
  (requires
    rsa_skey_pre modBits eBits dBits skey)
  (ensures
   (let valid, msg = rsa_dec_ modBits eBits dBits skey cipher in
    rsa_dec_post modBits eBits dBits skey cipher valid msg))

let rsa_dec_lemma #t modBits eBits dBits skey cipher =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n  = sub skey 0 nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  let k = blocks modBits 8 in
  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);
  Math.Lemmas.pow2_le_compat (8 * k) modBits;

  let c = bn_from_bytes_be k cipher in
  bn_from_bytes_be_lemma #t k cipher;

  let m_zero = bn_from_uint nLen (uint #t #SEC 0) in
  bn_from_uint_lemma nLen (uint #t #SEC 0);
  let lt_c = bn_lt_mask c n in
  bn_lt_mask_lemma c n;
  if BB.unsafe_bool_of_limb lt_c then begin
    Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
    SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;
    let s = bn_mod_exp_consttime_precompr2 nLen n r2 c dBits d in
    let c' = bn_mod_exp_vartime_precompr2 nLen n r2 s eBits e in
    let eq_c = bn_eq_mask c c' in
    bn_eq_mask_lemma c c';
    let s' = map (logand eq_c) s in
    bn_mask_lemma s eq_c;

    assert (bn_v s' < pow2 (8 * k));
    let msg = bn_to_bytes_be k s' in
    bn_to_bytes_be_lemma k s'
    end
  else begin
    let msg = bn_to_bytes_be k m_zero in
    bn_to_bytes_be_lemma k m_zero
  end


val rsa_enc_bn:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> m:lbignum t (blocks modBits (bits t)) ->
  Pure (tuple2 bool (lbignum t (blocks modBits (bits t))))
  (requires rsa_pkey_pre modBits eBits pkey)
  (ensures fun res -> True)

let rsa_enc_bn #t modBits eBits pkey m =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  let c_zero = bn_from_uint nLen (uint #t #SEC 0) in
  bn_from_uint_lemma nLen (uint #t #SEC 0);

  let mask = bn_lt_mask m n in
  bn_lt_mask_lemma m n;

  if BB.unsafe_bool_of_limb mask then begin
    Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
    SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;

    let c = bn_mod_exp_vartime_precompr2 nLen n r2 m eBits e in
    (true, c)
    end
  else false, c_zero


val rsa_enc_:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> msg:lseq uint8 (blocks modBits 8) ->
  Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires rsa_pkey_pre modBits eBits pkey)
  (ensures  fun res -> True)

let rsa_enc_ #t modBits eBits pkey msg =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let k = blocks modBits 8 in

  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);
  let m = bn_from_bytes_be k msg in
  let valid,c = rsa_enc_bn #t modBits eBits pkey m in
  valid,bn_to_bytes_be k c

val rsa_enc_lemma:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> msg:lseq uint8 (blocks modBits 8) -> Lemma
  (requires
    rsa_pkey_pre modBits eBits pkey)
  (ensures (
    let (valid,cipher) = rsa_enc_ modBits eBits pkey msg in
    rsa_enc_post modBits eBits pkey msg valid cipher))

let rsa_enc_lemma #t modBits eBits pkey msg =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let k = blocks modBits 8 in

  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);

  let m = bn_from_bytes_be k msg in
  bn_from_bytes_be_lemma #t k msg;

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  let c_zero = bn_from_uint nLen (uint #t #SEC 0) in
  bn_from_uint_lemma nLen (uint #t #SEC 0);

  let mask = bn_lt_mask m n in
  bn_lt_mask_lemma m n;

  if BB.unsafe_bool_of_limb mask then begin
    Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
    SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;
    let c = bn_mod_exp_vartime_precompr2 nLen n r2 m eBits e in
    assert (bn_v c < bn_v n);
    assert (bn_v c < pow2 modBits);
    assert (modBits <= k * 8);
    Math.Lemmas.pow2_le_compat (k * 8) modBits;
    let cipher = bn_to_bytes_be k c in
    bn_to_bytes_be_lemma k c
    end
  else begin
    let cipher = bn_to_bytes_be k c_zero in
    bn_to_bytes_be_lemma k c_zero
  end


val bn_check_num_bits: #t:limb_t -> bs:size_pos -> b:lbignum t (blocks bs (bits t)) ->
  res:limb t{v res == (if bn_v b < pow2 bs then v (ones t SEC) else v (zeros t SEC))}

let bn_check_num_bits #t bs b =
  let bLen = blocks bs (bits t) in
  assert (bs <= bits t * bLen);
  let m : limb t = if bs = bits t * bLen then ones t SEC else bn_lt_pow2_mask b bs in
  (if bs = bits t * bLen then begin
    bn_eval_bound b bLen;
    Math.Lemmas.pow2_le_compat (bits t * bLen) bs end
  else
    bn_lt_pow2_mask_lemma b bs);
  assert (v m == (if bn_v b < pow2 bs then v (ones t SEC) else v (zeros t SEC)));
  m


val rsa_check_modulus: #t:limb_t -> modBits:size_pos -> n:lbignum t (blocks modBits (bits t)) ->
  res:limb t{v res == (if (bn_v n % 2 = 1 && pow2 (modBits - 1) < bn_v n && bn_v n < pow2 modBits) then v (ones t SEC) else v (zeros t SEC))}

let rsa_check_modulus #t modBits n =
  let bit0 = bn_is_odd n in
  bn_is_odd_lemma n;
  assert (v bit0 == bn_v n % 2);
  let m0 = uint #t 0 -. bit0 in

  let m1 = bn_gt_pow2_mask n (modBits - 1) in
  bn_gt_pow2_mask_lemma n (modBits - 1);

  let m2 = bn_check_num_bits modBits n in
  let m = m0 &. (m1 &. m2) in
  logand_lemma m0 (m1 &. m2);
  logand_lemma m1 m2;
  m


val rsa_check_exponent: #t:limb_t -> eBits:size_pos -> e:lbignum t (blocks eBits (bits t)) ->
  res:limb t{v res == (if (0 < bn_v e && bn_v e < pow2 eBits) then v (ones t SEC) else v (zeros t SEC))}

let rsa_check_exponent #t eBits e =
  let m0 = bn_is_zero_mask e in
  bn_is_zero_mask_lemma e;
  let m1 = bn_check_num_bits eBits e in
  let m = (lognot m0) &. m1 in
  lognot_lemma m0;
  logand_lemma (lognot m0) m1;
  m


val rsa_load_pkey_post:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t)) -> Type0

let rsa_load_pkey_post #t modBits eBits nb eb pkey =
  let bits = bits t in
  let pkey_s = S.rsa_load_pkey modBits eBits nb eb in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0 nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  rsa_pkey_pre modBits eBits pkey /\
  Some? pkey_s /\
  bn_v n == S.Mk_rsa_pkey?.n (Some?.v pkey_s) /\
  bn_v e == S.Mk_rsa_pkey?.e (Some?.v pkey_s)



val rsa_load_skey_post:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8)
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t)) -> Type0

let rsa_load_skey_post #t modBits eBits dBits nb eb db skey =
  let bits = bits t in
  let skey_s = S.rsa_load_skey modBits eBits dBits nb eb db in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n  = sub skey 0 nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  rsa_skey_pre modBits eBits dBits skey /\
  Some? skey_s /\ (let pkey_s = S.Mk_rsa_skey?.pkey (Some?.v skey_s) in
  bn_v n == S.Mk_rsa_pkey?.n pkey_s /\
  bn_v e == S.Mk_rsa_pkey?.e pkey_s /\
  bn_v d == S.Mk_rsa_skey?.d (Some?.v skey_s))


val rsa_load_pkey:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  tuple2 bool (lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t)))

let rsa_load_pkey #t modBits eBits nb eb =
  let n  = bn_from_bytes_be (blocks modBits 8) nb in
  let r2 = SM.bn_precomp_r2_mod_n (modBits - 1) n in
  let e  = bn_from_bytes_be (blocks eBits 8) eb in
  let pkey = (n @| r2) @| e in

  let m0 = rsa_check_modulus modBits n in
  let m1 = rsa_check_exponent eBits e in
  let m = m0 &. m1 in
  BB.unsafe_bool_of_limb m, pkey


val rsa_load_pkey_lemma:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  Lemma
  (let b, pkey = rsa_load_pkey #t modBits eBits nb eb in
   let pkey_s = S.rsa_load_pkey modBits eBits nb eb in
   (if b then rsa_load_pkey_post modBits eBits nb eb pkey else None? pkey_s))

let rsa_load_pkey_lemma #t modBits eBits nb eb =
  let bits = bits t in
  let nbLen = blocks modBits 8 in
  let ebLen = blocks eBits 8 in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = bn_from_bytes_be #t nbLen nb in
  bn_from_bytes_be_lemma #t nbLen nb;
  let r2 = SM.bn_precomp_r2_mod_n (modBits - 1) n in
  let e  = bn_from_bytes_be #t ebLen eb in
  bn_from_bytes_be_lemma #t ebLen eb;

  let pkey = (n @| r2) @| e in
  eq_intro (sub pkey 0 nLen) n;
  eq_intro (sub pkey nLen nLen) r2;
  eq_intro (sub pkey (nLen + nLen) eLen) e;


  let m0 = rsa_check_modulus modBits n in
  let m1 = rsa_check_exponent eBits e in
  let m = m0 &. m1 in
  logand_lemma m0 m1


val rsa_load_skey:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  tuple2 bool (lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t)))

let rsa_load_skey #t modBits eBits dBits nb eb db =
  let b, pkey = rsa_load_pkey modBits eBits nb eb in
  let d = bn_from_bytes_be #t (blocks dBits 8) db in
  let skey = pkey @| d in

  let m0 = rsa_check_exponent dBits d in
  let b1 = b && BB.unsafe_bool_of_limb m0 in
  b1, skey


val rsa_load_skey_lemma:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  Lemma
  (let b, skey = rsa_load_skey #t modBits eBits dBits nb eb db in
   let skey_s = S.rsa_load_skey modBits eBits dBits nb eb db in
   (if b then rsa_load_skey_post modBits eBits dBits nb eb db skey else None? skey_s))

let rsa_load_skey_lemma #t modBits eBits dBits nb eb db =
  let bits = bits t in
  let nbLen = blocks modBits 8 in
  let ebLen = blocks eBits 8 in
  let dbLen = blocks dBits 8 in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let b, pkey = rsa_load_pkey #t modBits eBits nb eb in
  rsa_load_pkey_lemma #t modBits eBits nb eb;

  let d = bn_from_bytes_be #t (blocks dBits 8) db in
  bn_from_bytes_be_lemma #t (blocks dBits 8) db;

  let skey = pkey @| d in
  eq_intro (sub skey 0 (nLen + nLen + eLen)) pkey;
  eq_intro (sub skey (nLen + nLen + eLen) dLen) d

val rsa_dec:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8)
  -> cipher:lseq uint8 (blocks modBits 8)
  -> Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires True)
  (ensures  fun (b, msg) ->
    (b,msg) == S.rsa_dec modBits eBits dBits nb eb db cipher)

let rsa_dec #t modBits eBits dBits nb eb db cipher =
  let b, skey = rsa_load_skey #t modBits eBits dBits nb eb db in
  rsa_load_skey_lemma #t modBits eBits dBits nb eb db;

  if b then (
    rsa_dec_lemma modBits eBits dBits skey cipher;
    rsa_dec_ modBits eBits dBits skey cipher
  ) else 
    (false, create (blocks modBits 8) (uint 0))

val rsa_enc:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> msg:lseq uint8 (blocks modBits 8) ->
  Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires True)
  (ensures  fun (b,cipher) ->
    (b,cipher) == S.rsa_enc modBits eBits nb eb msg)

let rsa_enc #t modBits eBits nb eb msg =
  let b, pkey = rsa_load_pkey #t modBits eBits nb eb in
  rsa_load_pkey_lemma #t modBits eBits nb eb;

  if b then (
    rsa_enc_lemma modBits eBits pkey msg;
    rsa_enc_ modBits eBits pkey msg
  ) else 
    (false, create (blocks modBits 8) (uint 0))
