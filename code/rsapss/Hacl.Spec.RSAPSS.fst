module Hacl.Spec.RSAPSS

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Exponentiation

module S = Spec.RSAPSS
module BB = Hacl.Spec.Bignum.Base
module SM = Hacl.Spec.Bignum.Montgomery
module BSeq = Lib.ByteSequence
module Hash = Spec.Agile.Hash

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


val rsapss_pkey_pre:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t)) -> Type0

let rsapss_pkey_pre #t modBits eBits pkey =
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


val rsapss_skey_pre:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t)) -> Type0

let rsapss_skey_pre #t modBits eBits dBits skey =
  let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in
  let pkeyLen = nLen + nLen + eLen in

  let pkey = sub skey 0 pkeyLen in
  let d    = sub skey pkeyLen dLen in
  rsapss_pkey_pre modBits eBits pkey /\
  0 < bn_v d /\ bn_v d < pow2 dBits


val rsapss_sign_pre:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat{1 < modBits}
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Type0

let rsapss_sign_pre a modBits sLen salt msgLen msg =
  sLen + Hash.hash_length a + 8 <= max_size_t /\
  sLen + Hash.hash_length a + 8 <= Hash.max_input_length a /\
  sLen + Hash.hash_length a + 2 <= blocks (modBits - 1) 8 /\
  msgLen <= Hash.max_input_length a


val rsapss_sign_post:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> eq_m:bool
  -> sgnt:lseq uint8 (blocks modBits 8) -> Type0

let rsapss_sign_post #t a modBits eBits dBits skey sLen salt msgLen msg eq_m sgnt =
  rsapss_sign_pre a modBits sLen salt msgLen msg /\
  rsapss_skey_pre modBits eBits dBits skey /\
 (let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n = bn_v (sub skey 0 nLen) in
  let e = bn_v (sub skey (nLen + nLen) eLen) in
  let d = bn_v (sub skey (nLen + nLen + eLen) dLen) in
  let pkeys : S.rsapss_pkey modBits = S.Mk_rsapss_pkey n e in
  let skeys : S.rsapss_skey modBits = S.Mk_rsapss_skey pkeys d in
  let eq_m_s, sgnt_s = S.rsapss_sign_ a modBits skeys sLen salt msgLen msg in
  eq_m_s == eq_m /\ sgnt == sgnt_s)


val rsapss_sign_post1:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> eq_m:bool
  -> sgnt:lseq uint8 (blocks modBits 8) -> Type0

let rsapss_sign_post1 #t a modBits eBits dBits skey sLen salt msgLen msg eq_m sgnt =
  rsapss_skey_pre modBits eBits dBits skey /\
 (let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n = bn_v (sub skey 0 nLen) in
  let e = bn_v (sub skey (nLen + nLen) eLen) in
  let d = bn_v (sub skey (nLen + nLen + eLen) dLen) in
  let pkeys : S.rsapss_pkey modBits = S.Mk_rsapss_pkey n e in
  let skeys : S.rsapss_skey modBits = S.Mk_rsapss_skey pkeys d in
  let sgnt_s = S.rsapss_sign a modBits skeys sLen salt msgLen msg in
  if eq_m then Some? sgnt_s /\ sgnt == Some?.v sgnt_s else None? sgnt_s)


val rsapss_verify_pre:
    a:Hash.algorithm{S.hash_is_supported a}
  -> sLen:size_nat //saltLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Type0

let rsapss_verify_pre a sLen msgLen msg =
  sLen + Hash.hash_length a + 8 <= max_size_t /\
  sLen + Hash.hash_length a + 8 <= Hash.max_input_length a /\
  msgLen <= Hash.max_input_length a


val rsapss_verify_post:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> verify:bool -> Type0

let rsapss_verify_post #t a modBits eBits pkey sLen sgnt msgLen msg verify =
  rsapss_verify_pre a sLen msgLen msg /\
  rsapss_pkey_pre modBits eBits pkey /\
 (let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n = bn_v (sub pkey 0 nLen) in
  let e = bn_v (sub pkey (nLen + nLen) eLen) in
  let pkeys : S.rsapss_pkey modBits = S.Mk_rsapss_pkey n e in
  verify == S.rsapss_verify_ a modBits pkeys sLen sgnt msgLen msg)


val rsapss_verify_post1:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> sLen:size_nat //saltLen
  -> k:size_nat
  -> sgnt:lseq uint8 k
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> verify:bool -> Type0

let rsapss_verify_post1 #t a modBits eBits pkey sLen k sgnt msgLen msg verify =
  rsapss_pkey_pre modBits eBits pkey /\
 (let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n = bn_v (sub pkey 0 nLen) in
  let e = bn_v (sub pkey (nLen + nLen) eLen) in
  let pkeys : S.rsapss_pkey modBits = S.Mk_rsapss_pkey n e in
  verify == S.rsapss_verify a modBits pkeys sLen k sgnt msgLen msg)


val rsapss_sign_bn:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> m:lbignum t (blocks modBits (bits t)) ->
  Pure (tuple2 bool (lbignum t (blocks modBits (bits t))))
  (requires
   (let nLen = blocks modBits (bits t) in
    let n  = sub skey 0 nLen in
    rsapss_skey_pre modBits eBits dBits skey /\
    bn_v m < bn_v n))
  (ensures fun res -> True)

let rsapss_sign_bn #t modBits eBits dBits skey m =
  let bits = bits t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n  = sub skey 0 nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  let k = blocks modBits 8 in
  Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
  SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;
  let s = bn_mod_exp_fw_precompr2 nLen 4 n m dBits d r2 in
  let m' = bn_mod_exp_rl_precompr2 nLen n s eBits e r2 in
  let eq_m = bn_eq_mask m m' in
  let s = map (logand eq_m) s in
  BB.unsafe_bool_of_limb eq_m, s


val rsapss_sign_msg_to_bn:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat{1 < modBits}
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} ->
  Pure (lbignum t (blocks modBits (bits t)))
  (requires rsapss_sign_pre a modBits sLen salt msgLen msg)
  (ensures  fun res -> bn_v res < pow2 (modBits - 1))

let rsapss_sign_msg_to_bn #t a modBits sLen salt msgLen msg =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in

  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode a sLen salt msgLen msg emBits in
  blocks_bits_lemma t emBits;
  blocks_numb_lemma t emBits;
  assert (blocks emLen numb == blocks emBits bits);
  assert (numb * blocks emLen numb <= max_size_t);
  let emNat = bn_from_bytes_be #t emLen em in
  let m = create nLen (uint #t 0) in
  let m = update_sub m 0 (blocks emLen numb) emNat in
  bn_eval_update_sub (blocks emLen numb) emNat nLen;
  assert (bn_v m == bn_v emNat);
  bn_from_bytes_be_lemma #t emLen em;
  S.os2ip_lemma emBits em;
  m


val rsapss_sign_compute_sgnt:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> m:lbignum t (blocks modBits (bits t)) ->
  Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires
   (let nLen = blocks modBits (bits t) in
    let n  = sub skey 0 nLen in
    rsapss_skey_pre modBits eBits dBits skey /\
    bn_v m < bn_v n))
  (ensures fun res -> True)

let rsapss_sign_compute_sgnt #t modBits eBits dBits skey m =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let k = blocks modBits 8 in

  let eq_b, s = rsapss_sign_bn #t modBits eBits dBits skey m in
  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);
  let sgnt = bn_to_bytes_be k s in
  eq_b, sgnt


val rsapss_sign_:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} ->
  Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires
    rsapss_skey_pre modBits eBits dBits skey /\
    rsapss_sign_pre a modBits sLen salt msgLen msg)
  (ensures fun res -> True)


let rsapss_sign_ #t a modBits eBits dBits skey sLen salt msgLen msg =
  let m = rsapss_sign_msg_to_bn #t a modBits sLen salt msgLen msg in
  rsapss_sign_compute_sgnt #t modBits eBits dBits skey m


val rsapss_sign_lemma:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Lemma
  (requires
    rsapss_sign_pre a modBits sLen salt msgLen msg /\
    rsapss_skey_pre modBits eBits dBits skey)
  (ensures
   (let eq_m, s = rsapss_sign_ a modBits eBits dBits skey sLen salt msgLen msg in
    rsapss_sign_post a modBits eBits dBits skey sLen salt msgLen msg eq_m s))

let rsapss_sign_lemma #t a modBits eBits dBits skey sLen salt msgLen msg =
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
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode a sLen salt msgLen msg emBits in
  blocks_bits_lemma t emBits;
  blocks_numb_lemma t emBits;
  assert (blocks emLen numb == blocks emBits bits);
  assert (numb * blocks emLen numb <= max_size_t);

  let emNat = bn_from_bytes_be emLen em in
  let m = create nLen (uint #t 0) in
  let m = update_sub m 0 (blocks emLen numb) emNat in
  bn_eval_update_sub (blocks emLen numb) emNat nLen;
  assert (bn_v m == bn_v emNat);
  bn_from_bytes_be_lemma #t emLen em;
  S.os2ip_lemma emBits em;

  assert (bn_v m < bn_v n);
  Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
  SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;
  let s = bn_mod_exp_fw_precompr2 nLen 4 n m dBits d r2 in
  let m' = bn_mod_exp_rl_precompr2 nLen n s eBits e r2 in

  let eq_m = bn_eq_mask m m' in
  bn_eq_mask_lemma m m';

  let s' = map (logand eq_m) s in
  bn_mask_lemma s eq_m;

  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);
  Math.Lemmas.pow2_le_compat (8 * k) modBits;
  assert (bn_v s' < pow2 (8 * k));
  let sgnt = bn_to_bytes_be k s' in
  bn_to_bytes_be_lemma k s'


val rsapss_sign:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t))
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires rsapss_skey_pre modBits eBits dBits skey)
  (ensures  fun (b, sgnt) ->
    rsapss_sign_post1 a modBits eBits dBits skey sLen salt msgLen msg b sgnt)

let rsapss_sign #t a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  let hLen = Hash.hash_length a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  assert (max_size_t < Hash.max_input_length a);

  let b =
    sLen <= v (0xfffffffful) - hLen - 8 &&
    msgLen <= Hash.max_input_length a &&
    sLen + hLen + 2 <= blocks (modBits - 1) 8 in

  if b then begin
    rsapss_sign_lemma a modBits eBits dBits skey sLen salt msgLen msg;
    rsapss_sign_ a modBits eBits dBits skey sLen salt msgLen msg end
  else
    false, sgnt


val rsapss_verify_bn:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> m_def:lbignum t (blocks modBits (bits t))
  -> s:lbignum t (blocks modBits (bits t)) ->
  Pure (tuple2 bool (lbignum t (blocks modBits (bits t))))
  (requires rsapss_pkey_pre modBits eBits pkey)
  (ensures fun res -> True)

let rsapss_verify_bn #t modBits eBits pkey m_def s =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  let mask = bn_lt_mask s n in
  bn_lt_mask_lemma s n;

  if BB.unsafe_bool_of_limb mask then begin
    Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
    SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;

    let m = bn_mod_exp_rl_precompr2 nLen n s eBits e r2 in
    if bn_lt_pow2 modBits m then (true, m)
    else false, m end
  else false, m_def


val rsapss_verify_bn_to_msg:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat{1 < modBits}
  -> sLen:size_nat //saltLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> m:lbignum t (blocks modBits (bits t)) ->
  Pure bool
  (requires rsapss_verify_pre a sLen msgLen msg)
  (ensures  fun r -> True)

let rsapss_verify_bn_to_msg #t a modBits sLen msgLen msg m =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in

  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  blocks_bits_lemma t emBits;
  blocks_numb_lemma t emBits;
  assert (blocks emLen numb == blocks emBits bits);
  assert (numb * blocks emLen numb <= max_size_t);

  let m1 = sub m 0 (blocks emLen numb) in
  let em = bn_to_bytes_be emLen m1 in
  S.pss_verify a sLen msgLen msg emBits em


val rsapss_verify_compute_msg:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> sgnt:lseq uint8 (blocks modBits 8) ->
  Pure (tuple2 bool (lbignum t (blocks modBits (bits t))))
  (requires rsapss_pkey_pre modBits eBits pkey)
  (ensures  fun res -> True)

let rsapss_verify_compute_msg #t modBits eBits pkey sgnt =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let k = blocks modBits 8 in

  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);
  let s = bn_from_bytes_be k sgnt in

  let m_def = create nLen (uint #t 0) in
  rsapss_verify_bn #t modBits eBits pkey m_def s


val rsapss_verify_:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} ->
  Pure bool
  (requires
    rsapss_pkey_pre modBits eBits pkey /\
    rsapss_verify_pre a sLen msgLen msg)
  (ensures  fun r -> True)

let rsapss_verify_ #t a modBits eBits pkey sLen sgnt msgLen msg =
  let (b, m) = rsapss_verify_compute_msg #t modBits eBits pkey sgnt in
  if b then
    rsapss_verify_bn_to_msg a modBits sLen msgLen msg m
  else
    false


val rsapss_verify_lemma:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Lemma
  (requires
    rsapss_verify_pre a sLen msgLen msg /\
    rsapss_pkey_pre modBits eBits pkey)
  (ensures
    rsapss_verify_post a modBits eBits pkey sLen sgnt msgLen msg
      (rsapss_verify_ a modBits eBits pkey sLen sgnt msgLen msg))

let rsapss_verify_lemma #t a modBits eBits pkey sLen sgnt msgLen msg =
  let bits = bits t in
  let numb = numbytes t in
  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  blocks_bits_lemma t modBits;
  blocks_numb_lemma t modBits;
  assert (blocks k numb == nLen);
  assert (numb * blocks k numb <= max_size_t);
  let s = bn_from_bytes_be k sgnt in
  bn_from_bytes_be_lemma #t k sgnt;

  let mask = bn_lt_mask s n in
  bn_lt_mask_lemma s n;

  let res =
  if BB.unsafe_bool_of_limb mask then begin
    Math.Lemmas.pow2_le_compat (bits * nLen) modBits;
    SM.bn_precomp_r2_mod_n_lemma (modBits - 1) n;
    let m = bn_mod_exp_rl_precompr2 nLen n s eBits e r2 in

    blocks_bits_lemma t emBits;
    blocks_numb_lemma t emBits;
    assert (blocks emLen numb == blocks emBits bits);
    assert (numb * blocks emLen numb <= max_size_t);

    bn_lt_pow2_lemma modBits m;
    assert (bn_lt_pow2 modBits m == (bn_v m < pow2 (emLen * 8)));
    let res =
    if bn_lt_pow2 modBits m then begin
      let m1 = sub m 0 (blocks emLen numb) in
      bn_eval_sub modBits m;
      assert (bn_v m1 == bn_v m);
      let em = bn_to_bytes_be emLen m1 in
      bn_to_bytes_be_lemma emLen m1;
      S.pss_verify a sLen msgLen msg emBits em end
    else false in
    () end in
  ()


val rsapss_verify:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t))
  -> sLen:size_nat //saltLen
  -> k:size_nat
  -> sgnt:lseq uint8 k
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} ->
  Pure bool
  (requires rsapss_pkey_pre modBits eBits pkey)
  (ensures  fun r -> rsapss_verify_post1 a modBits eBits pkey sLen k sgnt msgLen msg r)

let rsapss_verify #t a modBits eBits pkey sLen k sgnt msgLen msg =
  let hLen = Hash.hash_length a in
  Math.Lemmas.pow2_lt_compat 61 32;
  Math.Lemmas.pow2_lt_compat 125 32;
  assert (max_size_t < Hash.max_input_length a);
  assert (hLen + 8 < max_size_t);

  let b =
    sLen <= v (0xfffffffful) - hLen - 8 &&
    msgLen <= Hash.max_input_length a &&
    k = blocks modBits 8 in

  if b then begin
    rsapss_verify_lemma a modBits eBits pkey sLen sgnt msgLen msg;
    rsapss_verify_ a modBits eBits pkey sLen sgnt msgLen msg end
  else
    false



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


val rsapss_check_modulus: #t:limb_t -> modBits:size_pos -> n:lbignum t (blocks modBits (bits t)) ->
  res:limb t{v res == (if (bn_v n % 2 = 1 && pow2 (modBits - 1) < bn_v n && bn_v n < pow2 modBits) then v (ones t SEC) else v (zeros t SEC))}

let rsapss_check_modulus #t modBits n =
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


val rsapss_check_exponent: #t:limb_t -> eBits:size_pos -> e:lbignum t (blocks eBits (bits t)) ->
  res:limb t{v res == (if (0 < bn_v e && bn_v e < pow2 eBits) then v (ones t SEC) else v (zeros t SEC))}

let rsapss_check_exponent #t eBits e =
  let m0 = bn_is_zero_mask e in
  bn_is_zero_mask_lemma e;
  let m1 = bn_check_num_bits eBits e in
  let m = (lognot m0) &. m1 in
  lognot_lemma m0;
  logand_lemma (lognot m0) m1;
  m


val rsapss_load_pkey_post:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> pkey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t)) -> Type0

let rsapss_load_pkey_post #t modBits eBits nb eb pkey =
  let bits = bits t in
  let pkey_s = S.rsapss_load_pkey modBits eBits nb eb in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in

  let n  = sub pkey 0 nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  rsapss_pkey_pre modBits eBits pkey /\
  Some? pkey_s /\
  bn_v n == S.Mk_rsapss_pkey?.n (Some?.v pkey_s) /\
  bn_v e == S.Mk_rsapss_pkey?.e (Some?.v pkey_s)



val rsapss_load_skey_post:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8)
  -> skey:lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t)) -> Type0

let rsapss_load_skey_post #t modBits eBits dBits nb eb db skey =
  let bits = bits t in
  let skey_s = S.rsapss_load_skey modBits eBits dBits nb eb db in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let n  = sub skey 0 nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  rsapss_skey_pre modBits eBits dBits skey /\
  Some? skey_s /\ (let pkey_s = S.Mk_rsapss_skey?.pkey (Some?.v skey_s) in
  bn_v n == S.Mk_rsapss_pkey?.n pkey_s /\
  bn_v e == S.Mk_rsapss_pkey?.e pkey_s /\
  bn_v d == S.Mk_rsapss_skey?.d (Some?.v skey_s))


val rsapss_load_pkey:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  tuple2 bool (lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t)))

let rsapss_load_pkey #t modBits eBits nb eb =
  let n  = bn_from_bytes_be (blocks modBits 8) nb in
  let r2 = SM.bn_precomp_r2_mod_n (modBits - 1) n in
  let e  = bn_from_bytes_be (blocks eBits 8) eb in
  let pkey = (n @| r2) @| e in

  let m0 = rsapss_check_modulus modBits n in
  let m1 = rsapss_check_exponent eBits e in
  let m = m0 &. m1 in
  BB.unsafe_bool_of_limb m, pkey


val rsapss_load_pkey_lemma:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  Lemma
  (let b, pkey = rsapss_load_pkey #t modBits eBits nb eb in
   let pkey_s = S.rsapss_load_pkey modBits eBits nb eb in
   (if b then rsapss_load_pkey_post modBits eBits nb eb pkey else None? pkey_s))

let rsapss_load_pkey_lemma #t modBits eBits nb eb =
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


  let m0 = rsapss_check_modulus modBits n in
  let m1 = rsapss_check_exponent eBits e in
  let m = m0 &. m1 in
  logand_lemma m0 m1


val rsapss_load_skey:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  tuple2 bool (lbignum t (2 * blocks modBits (bits t) + blocks eBits (bits t) + blocks dBits (bits t)))

let rsapss_load_skey #t modBits eBits dBits nb eb db =
  let b, pkey = rsapss_load_pkey modBits eBits nb eb in
  let d = bn_from_bytes_be #t (blocks dBits 8) db in
  let skey = pkey @| d in

  let m0 = rsapss_check_exponent dBits d in
  let b1 = b && BB.unsafe_bool_of_limb m0 in
  b1, skey


val rsapss_load_skey_lemma:
    #t:limb_t
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  Lemma
  (let b, skey = rsapss_load_skey #t modBits eBits dBits nb eb db in
   let skey_s = S.rsapss_load_skey modBits eBits dBits nb eb db in
   (if b then rsapss_load_skey_post modBits eBits dBits nb eb db skey else None? skey_s))

let rsapss_load_skey_lemma #t modBits eBits dBits nb eb db =
  let bits = bits t in
  let nbLen = blocks modBits 8 in
  let ebLen = blocks eBits 8 in
  let dbLen = blocks dBits 8 in

  let nLen = blocks modBits bits in
  let eLen = blocks eBits bits in
  let dLen = blocks dBits bits in

  let b, pkey = rsapss_load_pkey #t modBits eBits nb eb in
  rsapss_load_pkey_lemma #t modBits eBits nb eb;

  let d = bn_from_bytes_be #t (blocks dBits 8) db in
  bn_from_bytes_be_lemma #t (blocks dBits 8) db;

  let skey = pkey @| d in
  eq_intro (sub skey 0 (nLen + nLen + eLen)) pkey;
  eq_intro (sub skey (nLen + nLen + eLen) dLen) d


val rsapss_skey_sign:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre t modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires True)
  (ensures  fun (b, sgnt) ->
   (let sgnt_s = S.rsapss_skey_sign a modBits eBits dBits nb eb db sLen salt msgLen msg in
    if b then Some? sgnt_s /\ sgnt == Some?.v sgnt_s else None? sgnt_s))

let rsapss_skey_sign #t a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  let b, skey = rsapss_load_skey #t modBits eBits dBits nb eb db in
  rsapss_load_skey_lemma #t modBits eBits dBits nb eb db;

  if b then
    rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt
  else
    false, sgnt


val rsapss_pkey_verify:
    #t:limb_t
  -> a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre t modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> sLen:size_nat //saltLen
  -> k:size_nat
  -> sgnt:lseq uint8 k
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} ->
  Pure bool
  (requires True)
  (ensures  fun r ->
    r == S.rsapss_pkey_verify a modBits eBits nb eb sLen k sgnt msgLen msg)

let rsapss_pkey_verify #t a modBits eBits nb eb sLen k sgnt msgLen msg =
  let b, pkey = rsapss_load_pkey #t modBits eBits nb eb in
  rsapss_load_pkey_lemma #t modBits eBits nb eb;

  if b then
    rsapss_verify a modBits eBits pkey sLen k sgnt msgLen msg
  else
    false
