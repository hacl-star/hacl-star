module Hacl.Impl.FFDHE

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.FFDHE.Constants
open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module S = Spec.FFDHE
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module Lemmas = Hacl.Spec.FFDHE.Lemmas

module BN = Hacl.Bignum
module BM = Hacl.Bignum.Montgomery
module BE = Hacl.Bignum.Exponentiation
module SB = Hacl.Spec.Bignum
module SM = Hacl.Spec.Bignum.Montgomery
module SE = Hacl.Spec.Bignum.Exponentiation
module SD = Hacl.Spec.Bignum.Definitions

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let size_pos = x:size_t{v x > 0}

[@CInline]
let ffdhe_len (a:S.ffdhe_alg) : x:size_pos{v x = S.ffdhe_len a} =
  allow_inversion S.ffdhe_alg;
  match a with
  | S.FFDHE2048 -> 256ul
  | S.FFDHE3072 -> 384ul
  | S.FFDHE4096 -> 512ul
  | S.FFDHE6144 -> 768ul
  | S.FFDHE8192 -> 1024ul


inline_for_extraction noextract
let get_ffdhe_p (a:S.ffdhe_alg) :x:glbuffer pub_uint8 (ffdhe_len a)
  {witnessed x (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\ recallable x}
 =
  allow_inversion S.ffdhe_alg;
  match a with
  | S.FFDHE2048 -> ffdhe_p2048
  | S.FFDHE3072 -> ffdhe_p3072
  | S.FFDHE4096 -> ffdhe_p4096
  | S.FFDHE6144 -> ffdhe_p6144
  | S.FFDHE8192 -> ffdhe_p8192


inline_for_extraction noextract
val ffdhe_p_to_ps:
    a:S.ffdhe_alg
  -> p_s:lbuffer uint8 (ffdhe_len a) ->
  Stack unit
  (requires fun h -> live h p_s)
  (ensures  fun h0 _ h1 -> modifies (loc p_s) h0 h1 /\
    BSeq.nat_from_intseq_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) ==
    BSeq.nat_from_intseq_be (as_seq h1 p_s))

let ffdhe_p_to_ps a p_s =
  let p = get_ffdhe_p a in
  recall_contents p (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a));
  let len = ffdhe_len a in
  mapT len p_s secret p;
  BSeq.nat_from_intseq_be_public_to_secret (v len) (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a))


inline_for_extraction noextract
let ffdhe_bn_from_g_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) =
  g_n:lbignum t (blocks len (size (numbytes t))) ->
  Stack unit
  (requires fun h -> live h g_n /\ v len = S.ffdhe_len a /\
    as_seq h g_n == LSeq.create (v (blocks len (size (numbytes t)))) (uint #t 0))
  (ensures  fun h0 _ h1 -> modifies (loc g_n) h0 h1 /\
    bn_v h1 g_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_g (S.get_ffdhe_params a)))


inline_for_extraction noextract
val ffdhe_bn_from_g: #t:limb_t -> a:S.ffdhe_alg -> len:size_pos -> ffdhe_bn_from_g_st t a len
let ffdhe_bn_from_g #t a len g_n =
  recall_contents ffdhe_g2 S.ffdhe_g2;
  [@inline_let] let nLen = blocks len (size (numbytes t)) in

  push_frame ();
  let g = create 1ul (u8 0) in
  mapT 1ul g secret ffdhe_g2;
  BSeq.nat_from_intseq_be_public_to_secret 1 S.ffdhe_g2;

  let h0 = ST.get () in
  update_sub_f h0 g_n 0ul 1ul
    (fun h -> SB.bn_from_bytes_be 1 (as_seq h0 g))
    (fun _ -> BN.bn_from_bytes_be 1ul g (sub g_n 0ul 1ul));

  let h1 = ST.get () in
  SD.bn_eval_update_sub #t 1 (SB.bn_from_bytes_be 1 (as_seq h0 g)) (v nLen);
  assert (bn_v h1 g_n == SD.bn_v (SB.bn_from_bytes_be #t 1 (as_seq h0 g)));
  SB.bn_from_bytes_be_lemma #t 1 (as_seq h0 g);
  assert (bn_v h1 g_n == BSeq.nat_from_bytes_be (as_seq h0 g));
  pop_frame ()


inline_for_extraction noextract
let ffdhe_precomp_p_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
  let nLen = blocks len (size (numbytes t)) in
  p_r2_n:lbignum t (nLen +! nLen) ->
  Stack unit
  (requires fun h -> v len = S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == nLen /\ live h p_r2_n)
  (ensures  fun h0 _ h1 -> modifies (loc p_r2_n) h0 h1 /\
   (let p_n = gsub p_r2_n 0ul nLen in
    let r2_n = gsub p_r2_n nLen nLen in
    bn_v h1 p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\
    0 < bn_v h1 p_n /\ bn_v h1 r2_n == pow2 (2 * bits t * v nLen) % bn_v h1 p_n))


inline_for_extraction noextract
val ffdhe_precomp_p:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t ->
  ffdhe_precomp_p_st t a len ke

let ffdhe_precomp_p #t a len ke p_r2_n =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let p_n = sub p_r2_n 0ul nLen in
  let r2_n = sub p_r2_n nLen nLen in

  let p_s = create len (u8 0) in
  ffdhe_p_to_ps a p_s;
  let h0 = ST.get () in
  BN.bn_from_bytes_be len p_s p_n;
  let h1 = ST.get () in
  SB.bn_from_bytes_be_lemma #t (v len) (as_seq h0 p_s);
  assert (bn_v h1 p_n == BSeq.nat_from_bytes_be (as_seq h0 p_s));
  S.ffdhe_p_lemma a;
  Lemmas.ffdhe_p_bits_lemma a;
  ke.BE.mont.BM.precomp (8ul *! len -! 1ul) p_n r2_n;
  SM.bn_precomp_r2_mod_n_lemma (8 * v len - 1) (as_seq h1 p_n);
  pop_frame ()


inline_for_extraction noextract
let new_ffdhe_precomp_p_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
  let nLen = blocks len (size (numbytes t)) in
  r:HS.rid ->
  ST (B.buffer (limb t))
  (requires fun h -> v len = S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == nLen /\
    ST.is_eternal_region r)
  (ensures  fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    not (B.g_is_null res) ==> (
      B.len res == nLen +! nLen /\
      B.(fresh_loc (loc_buffer res) h0 h1) /\
      B.(loc_includes (loc_region_only false r) (loc_buffer res)) /\
     (let p_n = gsub (res <: lbignum t (nLen +! nLen)) 0ul nLen in
      let r2_n = gsub (res <: lbignum t (nLen +! nLen)) nLen nLen in
      bn_v h1 p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\
      0 < bn_v h1 p_n /\ bn_v h1 r2_n == pow2 (2 * bits t * v nLen) % bn_v h1 p_n)))


inline_for_extraction noextract
val new_ffdhe_precomp_p:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t
  -> ffdhe_precomp_p:ffdhe_precomp_p_st t a len ke ->
  new_ffdhe_precomp_p_st t a len ke

let new_ffdhe_precomp_p #t a len ke ffdhe_precomp_p r =
  let h0 = ST.get () in
  let nLen = blocks len (size (numbytes t)) in
  assert (v (nLen +! nLen) > 0);
  let res = LowStar.Monotonic.Buffer.mmalloc_partial r (uint #t #SEC 0) (nLen +! nLen) in
  if B.is_null res then
    res
  else
    let h1 = ST.get () in
    B.(modifies_only_not_unused_in loc_none h0 h1);
    assert (B.len res == nLen +! nLen);
    let res: Lib.Buffer.buffer (limb t) = res in
    assert (B.length res == v nLen + v nLen);
    let res: lbignum t (nLen +! nLen) = res in
    ffdhe_precomp_p res;
    let h2 = ST.get () in
    B.(modifies_only_not_unused_in loc_none h0 h2);
    res


inline_for_extraction noextract
let ffdhe_compute_exp_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
  let nLen = blocks len (size (numbytes t)) in
     p_r2_n:lbignum t (nLen +! nLen)
  -> sk_n:lbignum t nLen
  -> b_n:lbignum t nLen
  -> res:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> v len == S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == nLen /\
    live h p_r2_n /\ live h sk_n /\ live h b_n /\ live h res /\
    disjoint p_r2_n res /\ disjoint sk_n res /\ disjoint b_n res /\ disjoint p_r2_n b_n /\
    disjoint p_r2_n sk_n /\
   (let p_n = gsub p_r2_n 0ul nLen in let r2_n = gsub p_r2_n nLen nLen in
    bn_v h p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\
    0 < bn_v h p_n /\ bn_v h r2_n == pow2 (2 * bits t * v nLen) % bn_v h p_n /\
    bn_v h b_n < bn_v h p_n - 1 /\ 1 < bn_v h sk_n))
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
   (S.ffdhe_p_lemma a;
    let res_n = Lib.NatMod.pow_mod #(bn_v h0 (gsub p_r2_n 0ul nLen)) (bn_v h0 b_n) (bn_v h0 sk_n) in
    as_seq h1 res == BSeq.nat_to_bytes_be (v len) res_n))


#push-options "--z3rlimit 100"
inline_for_extraction noextract
val ffdhe_compute_exp:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t ->
  ffdhe_compute_exp_st t a len ke

let ffdhe_compute_exp #t a len ke p_r2_n sk_n b_n res =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let p_n = sub p_r2_n 0ul nLen in
  let r2_n = sub p_r2_n nLen nLen in

  let res_n = create nLen (uint #t #SEC 0) in

  let h1 = ST.get () in
  S.ffdhe_p_lemma a;
  assert_norm (pow2 4 = 16);
  assert_norm (pow2 10 = 1024);
  Math.Lemmas.pow2_plus 4 10;
  Math.Lemmas.pow2_lt_compat 32 14;

  SD.bn_eval_bound #t (as_seq h1 sk_n) (v nLen);
  ke.BE.exp_fw_ct_precomp 4ul p_n b_n (size (bits t) *! nLen) sk_n r2_n res_n; //b_n ^ sk_n % p_n

  let h2 = ST.get () in
  BN.bn_to_bytes_be len res_n res;
  SB.bn_to_bytes_be_lemma (v len) (as_seq h2 res_n);
  pop_frame ()
#pop-options


inline_for_extraction noextract
let ffdhe_secret_to_public_precomp_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
  let nLen = blocks len (size (numbytes t)) in
    p_r2_n:lbignum t (nLen +! nLen)
  -> sk:lbuffer uint8 len
  -> pk:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> v len == S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == nLen /\
    live h sk /\ live h pk /\ live h p_r2_n /\
    disjoint sk pk /\ disjoint sk p_r2_n /\ disjoint pk p_r2_n /\
    1 < Lib.ByteSequence.nat_from_bytes_be (as_seq h sk) /\
   (let p_n = gsub p_r2_n 0ul nLen in let r2_n = gsub p_r2_n nLen nLen in
    bn_v h p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\
    0 < bn_v h p_n /\ bn_v h r2_n == pow2 (2 * bits t * v nLen) % bn_v h p_n))
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.ffdhe_secret_to_public a (as_seq h0 sk))

//TODO: pass sBits?
inline_for_extraction noextract
val ffdhe_secret_to_public_precomp:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t
  -> ffdhe_compute_exp:ffdhe_compute_exp_st t a len ke ->
  ffdhe_secret_to_public_precomp_st t a len ke

let ffdhe_secret_to_public_precomp #t a len ke ffdhe_compute_exp p_r2_n sk pk =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let g_n = create nLen (uint #t #SEC 0) in
  ffdhe_bn_from_g a len g_n;

  let sk_n = create nLen (uint #t #SEC 0) in
  let h0 = ST.get () in
  BN.bn_from_bytes_be len sk sk_n;
  SB.bn_from_bytes_be_lemma #t (v len) (as_seq h0 sk);

  S.ffdhe_g2_lemma ();
  S.ffdhe_p_lemma a;
  ffdhe_compute_exp p_r2_n sk_n g_n pk;
  pop_frame ()


inline_for_extraction noextract
let ffdhe_secret_to_public_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
    sk:lbuffer uint8 len
  -> pk:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> v len == S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == blocks len (size (numbytes t)) /\
    live h sk /\ live h pk /\ disjoint sk pk /\
    1 < Lib.ByteSequence.nat_from_bytes_be (as_seq h sk))
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.ffdhe_secret_to_public a (as_seq h0 sk))

//TODO: pass sBits?
inline_for_extraction noextract
val ffdhe_secret_to_public:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t
  -> ffdhe_secret_to_public_precomp:ffdhe_secret_to_public_precomp_st t a len ke
  -> ffdhe_precomp_p:ffdhe_precomp_p_st t a len ke ->
  ffdhe_secret_to_public_st t a len ke

let ffdhe_secret_to_public #t a len ke ffdhe_secret_to_public_precomp ffdhe_precomp_p sk pk =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let p_r2_n = create (nLen +! nLen) (uint #t #SEC 0) in
  ffdhe_precomp_p p_r2_n;

  ffdhe_secret_to_public_precomp p_r2_n sk pk;
  pop_frame ()


inline_for_extraction noextract
let ffdhe_check_pk_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) =
  let nLen = blocks len (size (numbytes t)) in
    pk_n:lbignum t nLen
  -> p_n:lbignum t nLen ->
  Stack (limb t)
  (requires fun h -> v len = S.ffdhe_len a /\
    live h pk_n /\ live h p_n /\ disjoint pk_n p_n /\
    bn_v h p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)))
  (ensures  fun h0 m h1 -> modifies0 h0 h1 /\
   v m == (if (1 < bn_v h0 pk_n && bn_v h0 pk_n < bn_v h0 p_n - 1) then v (ones t SEC) else 0))


inline_for_extraction noextract
val ffdhe_check_pk: #t:limb_t -> a:S.ffdhe_alg -> len:size_pos -> ffdhe_check_pk_st t a len
let ffdhe_check_pk #t a len pk_n p_n =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let p_n1 = create nLen (uint #t #SEC 0) in
  let h0 = ST.get () in

  let c = BN.bn_sub1 nLen p_n (uint #t 1) p_n1 in
  SB.bn_sub1_lemma (as_seq h0 p_n) (uint #t 1);
  let h1 = ST.get () in
  S.ffdhe_p_lemma a;
  SD.bn_eval_bound (as_seq h1 p_n1) (v nLen);
  assert (bn_v h1 p_n1 == bn_v h0 p_n - 1);

  let m0 = BN.bn_gt_pow2_mask nLen pk_n 0ul in
  SB.bn_gt_pow2_mask_lemma (as_seq h1 pk_n) 0;
  assert_norm (pow2 0 = 1);
  assert (if v m0 = 0 then 1 >= bn_v h1 pk_n else 1 < bn_v h1 pk_n);

  let m1 = BN.bn_lt_mask nLen pk_n p_n1 in
  SB.bn_lt_mask_lemma (as_seq h1 pk_n) (as_seq h1 p_n1);
  assert (if v m1 = 0 then bn_v h1 pk_n >= bn_v h1 p_n1 else bn_v h1 pk_n < bn_v h1 p_n1);

  let m = m0 &. m1 in
  logand_lemma m0 m1;
  pop_frame ();
  m


inline_for_extraction noextract
let ffdhe_shared_secret_precomp_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
  let nLen = blocks len (size (numbytes t)) in
    p_r2_n:lbignum t (nLen +! nLen)
  -> sk:lbuffer uint8 len
  -> pk:lbuffer uint8 len
  -> ss:lbuffer uint8 len ->
  Stack (limb t)
  (requires fun h -> v len = S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == nLen /\
    live h sk /\ live h pk /\ live h ss /\ live h p_r2_n /\
    disjoint sk pk /\ disjoint sk ss /\ disjoint pk ss /\
    disjoint p_r2_n ss /\ disjoint p_r2_n pk /\ disjoint p_r2_n sk /\
    1 < Lib.ByteSequence.nat_from_bytes_be (as_seq h sk) /\
   (let p_n = gsub p_r2_n 0ul nLen in let r2_n = gsub p_r2_n nLen nLen in
    bn_v h p_n == BSeq.nat_from_bytes_be (S.Mk_ffdhe_params?.ffdhe_p (S.get_ffdhe_params a)) /\
    0 < bn_v h p_n /\ bn_v h r2_n == pow2 (2 * bits t * v nLen) % bn_v h p_n))
  (ensures  fun h0 m h1 -> modifies (loc ss) h0 h1 /\
   (let ss_s = S.ffdhe_shared_secret a (as_seq h0 sk) (as_seq h0 pk) in
    if v m = v (ones t SEC) then Some? ss_s /\ as_seq h1 ss == Some?.v ss_s else None? ss_s))


inline_for_extraction noextract
val ffdhe_shared_secret_precomp:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t
  -> ffdhe_check_pk:ffdhe_check_pk_st t a len
  -> ffdhe_compute_exp:ffdhe_compute_exp_st t a len ke ->
  ffdhe_shared_secret_precomp_st t a len ke

let ffdhe_shared_secret_precomp #t a len ke ffdhe_check_pk ffdhe_compute_exp p_r2_n sk pk ss =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let p_n = sub p_r2_n 0ul nLen in
  let sk_n = create nLen (uint #t #SEC 0) in
  let pk_n = create nLen (uint #t #SEC 0) in
  let h0 = ST.get () in
  BN.bn_from_bytes_be len sk sk_n;
  BN.bn_from_bytes_be len pk pk_n;
  SB.bn_from_bytes_be_lemma #t (v len) (as_seq h0 sk);
  SB.bn_from_bytes_be_lemma #t (v len) (as_seq h0 pk);

  S.ffdhe_p_lemma a;
  let m = ffdhe_check_pk pk_n p_n in
  if Hacl.Bignum.Base.unsafe_bool_of_limb m then
    ffdhe_compute_exp p_r2_n sk_n pk_n ss;
  pop_frame ();
  m


inline_for_extraction noextract
let ffdhe_shared_secret_st (t:limb_t) (a:S.ffdhe_alg) (len:size_pos) (ke:BE.exp t) =
    sk:lbuffer uint8 len
  -> pk:lbuffer uint8 len
  -> ss:lbuffer uint8 len ->
  Stack (limb t)
  (requires fun h -> v len = S.ffdhe_len a /\
    ke.BE.mont.BM.bn.BN.len == blocks len (size (numbytes t)) /\
    live h sk /\ live h pk /\ live h ss /\
    disjoint sk pk /\ disjoint sk ss /\ disjoint pk ss /\
    1 < Lib.ByteSequence.nat_from_bytes_be (as_seq h sk))
  (ensures  fun h0 m h1 -> modifies (loc ss) h0 h1 /\
   (let ss_s = S.ffdhe_shared_secret a (as_seq h0 sk) (as_seq h0 pk) in
    if v m = v (ones t SEC) then Some? ss_s /\ as_seq h1 ss == Some?.v ss_s else None? ss_s))


inline_for_extraction noextract
val ffdhe_shared_secret:
    #t:limb_t
  -> a:S.ffdhe_alg
  -> len:size_pos
  -> ke:BE.exp t
  -> ffdhe_shared_secret_precomp:ffdhe_shared_secret_precomp_st t a len ke
  -> ffdhe_precomp_p:ffdhe_precomp_p_st t a len ke ->
  ffdhe_shared_secret_st t a len ke

let ffdhe_shared_secret #t a len ke ffdhe_shared_secret_precomp ffdhe_precomp_p sk pk ss =
  push_frame ();
  let nLen = blocks len (size (numbytes t)) in
  let p_n = create (nLen +! nLen) (uint #t #SEC 0) in
  ffdhe_precomp_p p_n;
  let m = ffdhe_shared_secret_precomp p_n sk pk ss in
  pop_frame ();
  m
