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

val em_blocks_lt_max_size_t: modBits:size_pos{1 < modBits} -> Lemma
  (requires 128 * blocks modBits 64 <= max_size_t)
  (ensures  8 * blocks (blocks (modBits - 1) 8) 8 <= max_size_t)
let em_blocks_lt_max_size_t modBits = ()
  // let r = 8 * blocks (blocks (modBits - 1) 8) 8 in
  // calc (==) {
  //   r;
  //   (==) { }
  //   8 * (((modBits - 2) / 8) / 8 + 1);
  //   (==) { Math.Lemmas.division_multiplication_lemma (modBits - 2) 8 8 }
  //   8 * ((modBits - 2) / 64 + 1);
  //   (==) { }
  //   8 * blocks (modBits - 1) 64;
  //   }

val blocks_bits_lemma: bits:size_pos ->
  Lemma (blocks (blocks bits 8) 8 == blocks bits 64)
let blocks_bits_lemma bits = ()

val blocks_bits_lemma1: bits:size_pos{64 * blocks bits 64 <= max_size_t} ->
  Lemma (8 * blocks bits 8 <= max_size_t)
let blocks_bits_lemma1 bits = ()

val bn_eval_lt_pow2_modBits: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> Lemma
  (requires bn_v m < pow2 modBits)
  (ensures  bn_v m == (bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1))

let bn_eval_lt_pow2_modBits modBits m =
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

val bn_lt_pow2: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> bool
let bn_lt_pow2 modBits m =
  if (modBits - 1) % 8 <> 0 then true
  else FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 (bn_get_ith_bit m (modBits - 1)) =^ 0uL)

val bn_lt_pow2_lemma: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> Lemma
  (requires bn_v m < pow2 modBits)
  (ensures  bn_lt_pow2 modBits m == (bn_v m < pow2 (8 * blocks (modBits - 1) 8)))

let bn_lt_pow2_lemma modBits m =
  let k = blocks modBits 8 in
  let emLen = blocks (modBits - 1) 8 in
  let mLen = blocks emLen 8 in
  let nLen = blocks k 8 in
  assert (nLen == blocks modBits 64);

  if (modBits - 1) % 8 <> 0 then Math.Lemmas.pow2_le_compat (8 * emLen) modBits
  else begin
    assert (k == emLen + 1);
    bn_eval_unfold_i m nLen;
    assert (8 * k == modBits + 7);
    assert (8 * emLen == modBits - 1);

    bn_eval_lt_pow2_modBits modBits m;
    let r = FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 (bn_get_ith_bit m (modBits - 1)) =^ 0uL) in
    bn_get_ith_bit_lemma m (modBits - 1) end


val bn_eval_sub: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> Lemma
  (requires bn_v m < pow2 (8 * blocks (modBits - 1) 8))
  (ensures  bn_v m == bn_v (sub m 0 (blocks (blocks (modBits - 1) 8) 8)))

let bn_eval_sub modBits m =
  let emLen = blocks (modBits - 1) 8 in
  let mLen = blocks emLen 8 in
  let nLen = blocks modBits 64 in
  assert (bn_v m < pow2 (8 * emLen));
  let m1 = sub m 0 mLen in
  bn_eval_split_i m mLen;
  assert (bn_v m == bn_v m1 + pow2 (64 * mLen) * bn_v (slice m mLen nLen));
  bn_eval_bound m1 mLen;
  assert (bn_v m1 < pow2 (64 * mLen));
  Math.Lemmas.pow2_le_compat (64 * mLen) (8 * emLen)


let pkey_len_pre (modBits:size_nat) (eBits:size_nat) =
  1 < modBits /\ 0 < eBits /\
  128 * blocks modBits 64 <= max_size_t /\
  64 * blocks eBits 64 <= max_size_t /\
  2 * blocks modBits 64 + blocks eBits 64 <= max_size_t


let skey_len_pre (modBits:size_nat) (eBits:size_nat) (dBits:size_nat) =
  pkey_len_pre modBits eBits /\
  0 < dBits /\ 64 * blocks dBits 64 <= max_size_t /\
  2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64 <= max_size_t


val rsapss_pkey_pre:
    modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> pkey:lbignum (2 * blocks modBits 64 + blocks eBits 64) -> Type0

let rsapss_pkey_pre modBits eBits pkey =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e = sub pkey (nLen + nLen) eLen in
  r2 == SM.precomp_r2_mod_n n /\
  bn_v n % 2 = 1 /\
  pow2 (modBits - 1) < bn_v n /\ bn_v n < pow2 modBits /\
  0 < bn_v e /\ bn_v e < pow2 eBits


val rsapss_skey_pre:
    modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> skey:lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64) -> Type0

let rsapss_skey_pre modBits eBits dBits skey =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in
  let pkeyLen = nLen + nLen + eLen in

  let pkey = sub skey 0 pkeyLen in
  let d    = sub skey pkeyLen dLen in
  rsapss_pkey_pre modBits eBits pkey /\
  0 < bn_v d /\ bn_v d < pow2 dBits


val rsapss_sign_pre:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> skey:lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Type0

let rsapss_sign_pre a modBits eBits dBits skey sLen salt msgLen msg =
  sLen + Hash.hash_length a + 8 <= max_size_t /\
  sLen + Hash.hash_length a + 8 <= Hash.max_input_length a /\
  sLen + Hash.hash_length a + 2 <= (blocks (modBits - 1) 8) /\
  msgLen <= Hash.max_input_length a /\

  rsapss_skey_pre modBits eBits dBits skey


val rsapss_sign_post:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> skey:lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> eq_m:bool
  -> sgnt:lseq uint8 (blocks modBits 8) -> Type0

let rsapss_sign_post a modBits eBits dBits skey sLen salt msgLen msg eq_m sgnt =
  rsapss_sign_pre a modBits eBits dBits skey sLen salt msgLen msg /\
 (let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n = bn_v (sub skey 0 nLen) in
  let e = bn_v (sub skey (nLen + nLen) eLen) in
  let d = bn_v (sub skey (nLen + nLen + eLen) dLen) in
  let pkeys : S.rsapss_pkey modBits = S.Mk_rsapss_pkey n e in
  let skeys : S.rsapss_skey modBits = S.Mk_rsapss_skey pkeys d in
  let eq_m_s, sgnt_s = S.rsapss_sign_ a modBits skeys sLen salt msgLen msg in
  eq_m_s == eq_m /\ (eq_m ==> sgnt == sgnt_s))


val rsapss_verify_pre:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> pkey:lbignum (2 * blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Type0

let rsapss_verify_pre a modBits eBits pkey sLen msgLen msg =
  sLen + Hash.hash_length a + 8 <= max_size_t /\
  sLen + Hash.hash_length a + 8 <= Hash.max_input_length a /\
  msgLen <= Hash.max_input_length a /\

  rsapss_pkey_pre modBits eBits pkey


val rsapss_verify_post:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> pkey:lbignum (2 * blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> verify:bool -> Type0

let rsapss_verify_post a modBits eBits pkey sLen sgnt msgLen msg verify =
  rsapss_verify_pre a modBits eBits pkey sLen msgLen msg /\
 (let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n = bn_v (sub pkey 0 nLen) in
  let e = bn_v (sub pkey (nLen + nLen) eLen) in
  let pkeys : S.rsapss_pkey modBits = S.Mk_rsapss_pkey n e in
  verify == S.rsapss_verify_ a modBits pkeys sLen sgnt msgLen msg)



val rsapss_sign_:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> skey:lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen}
  -> Pure (tuple2 bool (lseq uint8 (blocks modBits 8)))
  (requires rsapss_sign_pre a modBits eBits dBits skey sLen salt msgLen msg)
  (ensures  fun sgnt -> True)

let rsapss_sign_ a modBits eBits dBits skey sLen salt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n  = sub skey 0 nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode a sLen salt msgLen msg emBits in
  em_blocks_lt_max_size_t modBits;
  assert (8 * blocks emLen 8 <= max_size_t);
  let emNat = bn_from_bytes_be emLen em in
  let m = create nLen (u64 0) in
  let m = update_sub m 0 (blocks emLen 8) emNat in

  let s = bn_mod_exp_mont_ladder_precompr2 nLen n m dBits d r2 in
  let m' = bn_mod_exp_precompr2 nLen n s eBits e r2 in
  let eq_m = bn_eq_mask m m' in
  let s = map (logand eq_m) s in

  blocks_bits_lemma modBits;
  assert (blocks k 8 == nLen);
  let sgnt = bn_to_bytes_be k s in
  BB.unsafe_bool_of_u64 eq_m, sgnt


val rsapss_sign_lemma:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> skey:lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Lemma
  (requires
    rsapss_sign_pre a modBits eBits dBits skey sLen salt msgLen msg)
  (ensures
   (let eq_m, s = rsapss_sign_ a modBits eBits dBits skey sLen salt msgLen msg in
    rsapss_sign_post a modBits eBits dBits skey sLen salt msgLen msg eq_m s))

let rsapss_sign_lemma a modBits eBits dBits skey sLen salt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n  = sub skey 0 nLen in
  let r2 = sub skey nLen nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode a sLen salt msgLen msg emBits in
  em_blocks_lt_max_size_t modBits;
  assert (8 * blocks emLen 8 <= max_size_t);

  let emNat = bn_from_bytes_be emLen em in
  let m = create nLen (u64 0) in
  let m = update_sub m 0 (blocks emLen 8) emNat in
  bn_eval_update_sub (blocks emLen 8) emNat nLen;
  assert (bn_v m == bn_v emNat);
  bn_from_bytes_be_lemma emLen em;
  S.os2ip_lemma emBits em;

  assert (bn_v m < bn_v n);
  let s = bn_mod_exp_mont_ladder_precompr2 nLen n m dBits d r2 in
  Math.Lemmas.pow2_le_compat (64 * nLen) modBits;
  SM.precomp_r2_mod_n_lemma n;
  bn_mod_exp_mont_ladder_precompr2_lemma nLen n m dBits d r2;

  let m' = bn_mod_exp_precompr2 nLen n s eBits e r2 in
  bn_mod_exp_precompr2_lemma nLen n s eBits e r2;

  let eq_m = bn_eq_mask m m' in
  bn_eq_mask_lemma m m';

  let s' = map (logand eq_m) s in
  bn_mask_lemma s eq_m;

  blocks_bits_lemma modBits;
  assert (blocks k 8 == nLen);
  Math.Lemmas.pow2_le_compat (8 * k) modBits;
  assert (bn_v s' < pow2 (8 * k));
  let sgnt = bn_to_bytes_be k s' in
  bn_to_bytes_be_lemma k s'


val rsapss_verify_:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> pkey:lbignum (2 * blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} ->
  Pure bool
  (requires rsapss_verify_pre a modBits eBits pkey sLen msgLen msg)
  (ensures  fun r -> True)

let rsapss_verify_ a modBits eBits pkey sLen sgnt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  blocks_bits_lemma modBits;
  assert (blocks k 8 == nLen);
  let s = bn_from_bytes_be k sgnt in

  let mask = bn_lt_mask s n in
  if BB.unsafe_bool_of_u64 mask then begin
    let m = bn_mod_exp_precompr2 nLen n s eBits e r2 in
    em_blocks_lt_max_size_t modBits;
    assert (8 * blocks emLen 8 <= max_size_t);

    if bn_lt_pow2 modBits m then begin
      let m1 = sub m 0 (blocks emLen 8) in
      let em = bn_to_bytes_be emLen m1 in
      S.pss_verify a sLen msgLen msg emBits em end
    else false end
  else false


val rsapss_verify_lemma:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> pkey:lbignum (2 * blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:nat
  -> msg:seq uint8{length msg == msgLen} -> Lemma
  (requires
    rsapss_verify_pre a modBits eBits pkey sLen msgLen msg)
  (ensures
    rsapss_verify_post a modBits eBits pkey sLen sgnt msgLen msg
      (rsapss_verify_ a modBits eBits pkey sLen sgnt msgLen msg))

let rsapss_verify_lemma a modBits eBits pkey sLen sgnt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n  = sub pkey 0 nLen in
  let r2 = sub pkey nLen nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  blocks_bits_lemma modBits;
  assert (blocks k 8 == nLen);
  assert (8 * blocks k 8 <= max_size_t);
  let s = bn_from_bytes_be k sgnt in
  bn_from_bytes_be_lemma k sgnt;

  let mask = bn_lt_mask s n in
  bn_lt_mask_lemma s n;

  let res =
  if BB.unsafe_bool_of_u64 mask then begin
    let m = bn_mod_exp_precompr2 nLen n s eBits e r2 in
    Math.Lemmas.pow2_le_compat (64 * nLen) modBits;
    SM.precomp_r2_mod_n_lemma n;
    bn_mod_exp_precompr2_lemma nLen n s eBits e r2;
    em_blocks_lt_max_size_t modBits;
    assert (8 * blocks emLen 8 <= max_size_t);

    bn_lt_pow2_lemma modBits m;
    let res =
    if bn_lt_pow2 modBits m then begin
      let m1 = sub m 0 (blocks emLen 8) in
      bn_eval_sub modBits m;
      assert (bn_v m1 == bn_v m);
      let em = bn_to_bytes_be emLen m1 in
      bn_to_bytes_be_lemma emLen m1;
      S.pss_verify a sLen msgLen msg emBits em end
    else false in
    () end in
  ()



val bn_check_num_bits: bits:size_pos -> b:lbignum (blocks bits 64) ->
  res:uint64{v res == (if bn_v b < pow2 bits then v (ones U64 SEC) else v (zeros U64 SEC))}

let bn_check_num_bits bits b =
  let bLen = blocks bits 64 in
  assert (bits <= 64 * bLen);
  let m : uint64 = if bits = 64 * bLen then ones U64 SEC else bn_lt_pow2_mask b bits in
  (if bits = 64 * bLen then begin
    bn_eval_bound b bLen;
    Math.Lemmas.pow2_le_compat (64 * bLen) bits end
  else
    bn_lt_pow2_mask_lemma b bits);
  assert (v m == (if bn_v b < pow2 bits then v (ones U64 SEC) else v (zeros U64 SEC)));
  m


val rsapss_check_modulus: modBits:size_pos -> n:lbignum (blocks modBits 64) ->
  res:uint64{v res == (if (bn_v n % 2 = 1 && pow2 (modBits - 1) < bn_v n && bn_v n < pow2 modBits) then v (ones U64 SEC) else v (zeros U64 SEC))}

let rsapss_check_modulus modBits n =
  let bit0 = bn_is_odd n in
  bn_is_odd_lemma n;
  assert (v bit0 == bn_v n % 2);
  let m0 = u64 0 -. bit0 in

  let m1 = bn_gt_pow2_mask n (modBits - 1) in
  bn_gt_pow2_mask_lemma n (modBits - 1);

  let m2 = bn_check_num_bits modBits n in
  let m = m0 &. (m1 &. m2) in
  logand_lemma m0 (m1 &. m2);
  logand_lemma m1 m2;
  m


val rsapss_check_exponent: eBits:size_pos -> e:lbignum (blocks eBits 64) ->
  res:uint64{v res == (if (0 < bn_v e && bn_v e < pow2 eBits) then v (ones U64 SEC) else v (zeros U64 SEC))}

let rsapss_check_exponent eBits e =
  let m0 = bn_is_zero_mask e in
  bn_is_zero_mask_lemma e;
  let m1 = bn_check_num_bits eBits e in
  let m = (lognot m0) &. m1 in
  lognot_lemma m0;
  logand_lemma (lognot m0) m1;
  m


val rsapss_load_pkey_post:
    modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> pkey:lbignum (2 * blocks modBits 64 + blocks eBits 64) -> Type0

let rsapss_load_pkey_post modBits eBits nb eb pkey =
  let pkey_s = S.rsapss_load_pkey modBits eBits nb eb in

  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n  = sub pkey 0 nLen in
  let e  = sub pkey (nLen + nLen) eLen in

  rsapss_pkey_pre modBits eBits pkey /\
  Some? pkey_s /\
  bn_v n == S.Mk_rsapss_pkey?.n (Some?.v pkey_s) /\
  bn_v e == S.Mk_rsapss_pkey?.e (Some?.v pkey_s)



val rsapss_load_skey_post:
    modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8)
  -> skey:lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64) -> Type0

let rsapss_load_skey_post modBits eBits dBits nb eb db skey =
  let skey_s = S.rsapss_load_skey modBits eBits dBits nb eb db in

  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n  = sub skey 0 nLen in
  let e  = sub skey (nLen + nLen) eLen in
  let d  = sub skey (nLen + nLen + eLen) dLen in

  rsapss_skey_pre modBits eBits dBits skey /\
  Some? skey_s /\ (let pkey_s = S.Mk_rsapss_skey?.pkey (Some?.v skey_s) in
  bn_v n == S.Mk_rsapss_pkey?.n pkey_s /\
  bn_v e == S.Mk_rsapss_pkey?.e pkey_s /\
  bn_v d == S.Mk_rsapss_skey?.d (Some?.v skey_s))


val rsapss_load_pkey:
    modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  tuple2 bool (lbignum (2 * blocks modBits 64 + blocks eBits 64))

let rsapss_load_pkey modBits eBits nb eb =
  let n  = bn_from_bytes_be (blocks modBits 8) nb in
  let r2 = SM.precomp_r2_mod_n n in
  let e  = bn_from_bytes_be (blocks eBits 8) eb in
  let pkey = (n @| r2) @| e in

  let m0 = rsapss_check_modulus modBits n in
  let m1 = rsapss_check_exponent eBits e in
  let m = m0 &. m1 in
  BB.unsafe_bool_of_u64 m, pkey


val rsapss_load_pkey_lemma:
    modBits:size_nat
  -> eBits:size_nat{pkey_len_pre modBits eBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  Lemma (let b, pkey = rsapss_load_pkey modBits eBits nb eb in
   (b ==> rsapss_load_pkey_post modBits eBits nb eb pkey))

let rsapss_load_pkey_lemma modBits eBits nb eb =
  let nbLen = blocks modBits 8 in
  let ebLen = blocks eBits 8 in

  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n  = bn_from_bytes_be nbLen nb in
  bn_from_bytes_be_lemma nbLen nb;
  let r2 = SM.precomp_r2_mod_n n in
  let e  = bn_from_bytes_be ebLen eb in
  bn_from_bytes_be_lemma ebLen eb;

  let pkey = (n @| r2) @| e in
  eq_intro (sub pkey 0 nLen) n;
  eq_intro (sub pkey nLen nLen) r2;
  eq_intro (sub pkey (nLen + nLen) eLen) e;


  let m0 = rsapss_check_modulus modBits n in
  let m1 = rsapss_check_exponent eBits e in
  let m = m0 &. m1 in
  logand_lemma m0 m1


val rsapss_load_skey:
    modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  tuple2 bool (lbignum (2 * blocks modBits 64 + blocks eBits 64 + blocks dBits 64))

let rsapss_load_skey modBits eBits dBits nb eb db =
  let b, pkey = rsapss_load_pkey modBits eBits nb eb in
  let d = bn_from_bytes_be (blocks dBits 8) db in
  let skey = pkey @| d in

  let m0 = rsapss_check_exponent dBits d in
  let b1 = b && BB.unsafe_bool_of_u64 m0 in
  b1, skey


val rsapss_load_skey_lemma:
    modBits:size_nat
  -> eBits:size_nat
  -> dBits:size_nat{skey_len_pre modBits eBits dBits}
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  Lemma (let b, skey = rsapss_load_skey modBits eBits dBits nb eb db in
   (b ==> rsapss_load_skey_post modBits eBits dBits nb eb db skey))

let rsapss_load_skey_lemma modBits eBits dBits nb eb db =
  let nbLen = blocks modBits 8 in
  let ebLen = blocks eBits 8 in
  let dbLen = blocks dBits 8 in

  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let b, pkey = rsapss_load_pkey modBits eBits nb eb in
  rsapss_load_pkey_lemma modBits eBits nb eb;

  let d = bn_from_bytes_be (blocks dBits 8) db in
  bn_from_bytes_be_lemma (blocks dBits 8) db;

  let skey = pkey @| d in
  eq_intro (sub skey 0 (nLen + nLen + eLen)) pkey;
  eq_intro (sub skey (nLen + nLen + eLen) dLen) d
