module Hacl.Impl.HE.DGK

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Math.Algebra

open Hacl.Impl.Bignum
open Hacl.Impl.HE.Other

module S = Hacl.Spec.HE.DGK
//module Seq = Lib.Sequence
module Seq = FStar.Seq
module Seq' = FStar.Monotonic.Seq
module B = Lib.Buffer

let factors_list_proper (#bnlen:bn_len_s) (#len:size_t) (h:mem) (b:factors_list bnlen len) =
  let b' = as_snat_list_factors #bnlen #len h b in
  (forall (i:nat{i < Seq.length b'}). let (p,e) = Seq.index b' i in isprm p /\ e > 0) /\
  Seq.length b' > 0 /\
  S.is_crt_base b'

val proper_factor_list_matches_spec:
     #bnlen:bn_len_s
  -> #len:size_t
  -> h:mem
  -> factors:factors_list bnlen len{factors_list_proper h factors}
  -> Lemma (S.is_crt_base (as_snat_list_factors #bnlen #len h factors))
let proper_factor_list_matches_spec #bnlen #len h factors = ()


let values_list (bnlen:bn_len_s) (len:size_t) =
  lbuffer (lbignum bnlen) len

let values_list_proper (#bnlen:bn_len_s) (#len:size_t) (h:mem)
                   (factors:factors_list bnlen len) (values:bn_list bnlen len) =
  let factors' = as_snat_list_factors #bnlen #len h factors in
  let values' = as_snat_list_bn #bnlen #len h values in
  (forall (i:nat{i < Seq.length values'}).
    let a = Seq.index values' i in
    let (p,e) = Seq.index factors' i in
    a > 0 /\ a < exp p e)

val proper_values_list_matches_spec:
     #bnlen:bn_len_s
  -> #len:size_t
  -> h:mem
  -> factors:factors_list bnlen len{factors_list_proper h factors}
  -> values:values_list bnlen len{values_list_proper h factors values}
  -> Lemma (S.is_crt_values (as_snat_list_factors #bnlen #len h factors)
                            (as_snat_list_bn #bnlen #len h values))
let proper_values_list_matches_spec #bnlen #len h factors values = ()

// for all buffer elements
let forall_bufel (#len:size_t) (#a:Type) (h:mem) (bufl:lbuffer a len) (p:a -> Type) =
  let bufl = as_seq h bufl in
  (forall (i:nat{i < Seq.length bufl}). p (Seq.index bufl i))


type n_cond (h:mem) (#nLen:bn_len_s) (n:lbignum nLen) = as_snat h n > 1 /\ iscomp (as_snat h n)

noeq
type secret (nLen:bn_len_s) =
  | Sec:
     p:lbignum nLen
  -> q:lbignum nLen
  -> n:lbignum nLen
  -> u:lbignum nLen
  -> v:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen
  -> secret nLen

type proper_secret_raw
  (hp:mem)
  (#nLen:bn_len_s)
  (p:lbignum nLen)
  (q:lbignum nLen)
  (n:lbignum nLen)
  (u:lbignum nLen)
  (v:lbignum nLen)
  (g:lbignum nLen)
  (h:lbignum nLen) =
       n_cond hp #nLen n /\
       (let n = as_snat hp n in
        let p = as_snat hp p in
        let q = as_snat hp q in
        let u = as_snat hp u in
        let v = as_snat hp v in
        let g = as_snat hp g in
        let h = as_snat hp h in
        (p > 1 /\ q > 1 /\ isprm p /\ isprm q /\ p <> q /\ n = p * q /\

         u > 1 /\ u < n /\ divides u (p-1) /\ divides u (q-1) /\
         v > 1 /\ v < n /\ divides v (p-1) /\ divides v (q-1) /\

         g < n /\ isunit #(p*q) g /\ mult_order #(p*q) g = u * v /\

         h < n /\ S.is_h p q v h))

type proper_secret h (#nLen:bn_len_s) (s:secret nLen) =
  proper_secret_raw h
    (Sec?.p s)
    (Sec?.q s)
    (Sec?.n s)
    (Sec?.u s)
    (Sec?.v s)
    (Sec?.g s)
    (Sec?.h s)

type secret_mem h (#nLen:bn_len_s) (s:secret nLen) =
    live h (Sec?.p s) /\
    live h (Sec?.q s) /\
    live h (Sec?.n s) /\
    live h (Sec?.u s) /\
    live h (Sec?.v s) /\
    live h (Sec?.g s) /\
    live h (Sec?.h s) /\
    all_disjoint [loc (Sec?.p s);
                  loc (Sec?.q s);
                  loc (Sec?.n s);
                  loc (Sec?.u s);
                  loc (Sec?.v s);
                  loc (Sec?.g s);
                  loc (Sec?.h s)]


val as_spec_sk:
     #nLen:bn_len_s
  -> hp:mem
  -> s:secret nLen{secret_mem hp s /\ proper_secret hp s}
  -> GTot (s':S.secret)
let as_spec_sk #nLen hp s =
  S.Secret (as_snat hp (Sec?.p s))
           (as_snat hp (Sec?.q s))
           (as_snat hp (Sec?.u s))
           (as_snat hp (Sec?.v s))
           (as_snat hp (Sec?.g s))
           (as_snat hp (Sec?.h s))

noeq
type public (nLen:bn_len_s) =
  | Pub:
     n:lbignum nLen
  -> u:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen
  -> public nLen

type proper_public_raw
  (hp:mem)
  (#nLen:bn_len_s)
  (n:lbignum nLen)
  (u:lbignum nLen)
  (g:lbignum nLen)
  (h:lbignum nLen) =
       n_cond hp #nLen n /\
       (let n = as_snat hp n in
        let u = as_snat hp u in
        let g = as_snat hp g in
        let h = as_snat hp h in

        (u > 1 /\ u < n /\ g < n /\ h < n /\ isunit #n g /\ isunit #n h))

type proper_public h (#nLen:bn_len_s) (p:public nLen) =
  proper_public_raw h
    (Pub?.n p)
    (Pub?.u p)
    (Pub?.g p)
    (Pub?.h p)

type public_mem h (#nLen:bn_len_s) (p:public nLen) =
    live h (Pub?.n p) /\
    live h (Pub?.u p) /\
    live h (Pub?.g p) /\
    live h (Pub?.h p) /\
    all_disjoint [loc (Pub?.n p);
                  loc (Pub?.u p);
                  loc (Pub?.g p);
                  loc (Pub?.h p)]

val as_spec_pk:
     #nLen:bn_len_s
  -> hp:mem
  -> p:public nLen{public_mem hp p /\ proper_public hp p}
  -> GTot (p':S.public)
let as_spec_pk #nLen hp p =
  S.Public (as_snat hp (Pub?.n p))
           (as_snat hp (Pub?.u p))
           (as_snat hp (Pub?.g p))
           (as_snat hp (Pub?.h p))

val s2p: #nLen:bn_len_s -> s:secret nLen ->
  Stack (public nLen)
        (requires fun h -> proper_secret h s /\ secret_mem h s)
        (ensures fun h0 p h1 ->
         h0 == h1 /\
         proper_public h1 p /\
         public_mem h1 p /\
         as_spec_pk h1 p = S.s2p (as_spec_sk h0 s))
let s2p #nLen s = Pub (Sec?.n s) (Sec?.u s) (Sec?.g s) (Sec?.h s)

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val encrypt:
     #nLen:bn_len_s
  -> pk:public nLen
  -> r:lbignum nLen
  -> m:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
     (requires fun h ->
      proper_public h pk /\ public_mem h pk /\
      as_snat h r > 1 /\
      as_snat h m < as_snat h (Pub?.u pk) /\
      live h r /\ live h m /\ live h res /\
      disjoint m (Pub?.g pk) /\
      disjoint (Pub?.h pk) r /\
      disjoint (Pub?.n pk) res)
     (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res = S.encrypt (as_spec_pk h0 pk) (as_snat h0 r) (as_snat h0 m)
      )
let encrypt #nLen pk r m res =
  bn_len_s_fits nLen;

  push_frame ();
  let hp0 = FStar.HyperStack.ST.get () in

  let tmp1 = create nLen (u64 0) in
  let tmp2 = create nLen (u64 0) in

  let n = Pub?.n pk in
  let g = Pub?.g pk in
  let h = Pub?.h pk in

  bn_modular_exp n g m tmp1;
  bn_modular_exp n h r tmp2;
  bn_modular_mul n tmp1 tmp2 res;

  let hp = FStar.HyperStack.ST.get () in
  to_fe_idemp #(as_snat hp0 n) (as_snat hp0 g);
  to_fe_idemp #(as_snat hp0 n) (as_snat hp0 h);
  assert (as_snat hp res =
          ( *% ) #(as_snat hp0 n)
          (mexp #(as_snat hp0 n) (as_snat hp0 g) (as_snat hp0 m))
          (mexp #(as_snat hp0 n) (as_snat hp0 h) (as_snat hp0 r))
         );

  pop_frame ()

val check_is_zero:
     #nLen:bn_len_s
  -> sk:secret nLen
  -> c:lbignum nLen
  -> Stack bool
     (requires fun h ->
      proper_secret h sk /\ secret_mem h sk /\
      as_snat h c < as_snat h (Sec?.u sk) /\
      live h c /\
      disjoint (Sec?.v sk) c)
     (ensures fun h0 b h1 ->
      modifies0 h0 h1 /\
      b = S.check_is_zero (as_spec_sk h0 sk) (as_snat h0 c)
      )
let check_is_zero #nLen sk c =
  bn_len_s_fits nLen;
  push_frame ();
  let hp0 = FStar.HyperStack.ST.get () in

  let tmp = create nLen (u64 0) in
  to_fe_idemp #(as_snat hp0 (Sec?.n sk)) (as_snat hp0 c);
  bn_modular_exp (Sec?.n sk) c (Sec?.v sk) tmp;

  let one:lbignum 1ul = bn_one #1ul in

  let b = bn_is_equal tmp one in

  pop_frame ();
  b

val carm_pe_impl:
     #nLen:bn_len_s
  -> p:lbignum nLen
  -> e:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
     (requires fun h ->
      live h p /\ live h e /\ live h res /\
      disjoint p res /\ disjoint e res /\
      isprm (as_snat h p) /\
      as_snat h e > 0 /\
      nat_fits (exp (as_snat h p) (as_snat h e)) nLen)
     (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res = carm_pe (as_snat h0 p) (as_snat h0 e))
let carm_pe_impl #nLen p e res =
  let hp0 = FStar.HyperStack.ST.get () in
  bn_len_s_fits nLen;
  exp_greater_than_power (as_snat hp0 p) (as_snat hp0 e);
  nat_fits_trans (as_snat hp0 e)
                 (exp (as_snat hp0 p) (as_snat hp0 e))
                 nLen;

  push_frame ();

  let e' = bn_copy e in
  let one:lbignum 1ul = bn_one #1ul in
  bn_sub_exact e' one e';

  let tmp = create nLen (u64 0) in

  let hp = FStar.HyperStack.ST.get () in
  exp_sub (as_snat hp p) (as_snat hp e') (as_snat hp e);
  nat_fits_trans (exp (as_snat hp p) (as_snat hp e'))
                 (exp (as_snat hp p) (as_snat hp e))
                 nLen;

  bn_exp p e res;
  bn_exp p e' tmp;
  bn_sub_exact res tmp res;

  pop_frame ()

val fermat_inv_pe:
     #nLen:bn_len_s
  -> p:lbignum nLen
  -> e:lbignum nLen
  -> a:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h p /\ live h e /\ live h a /\ live h res /\
      disjoint p res /\ disjoint a res /\ disjoint e res /\
      isprm (as_snat h p) /\
      as_snat h e > 0 /\
      as_snat h a < exp (as_snat h p) (as_snat h e) /\
      nat_fits (exp (as_snat h p) (as_snat h e)) nLen)
    (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res =
        S.fermat_inv_pe (as_snat h0 p) (as_snat h0 e) (as_snat h0 a))
let fermat_inv_pe #nLen p e a res =
  bn_len_s_fits nLen;
  push_frame ();

  let lam = create nLen (u64 0) in
  carm_pe_impl p e lam;

  let one:lbignum 1ul = bn_one #1ul in
  bn_sub_exact lam one lam;

  let hp = FStar.HyperStack.ST.get () in
  assert (as_snat hp lam = carm_pe (as_snat hp p) (as_snat hp e) - 1);

  let m = bn_copy p in
  bn_exp m e res; copy m res;

  bn_modular_exp m a lam res;

  let hp = FStar.HyperStack.ST.get () in
  to_fe_idemp #(as_snat hp m) (as_snat hp a);

  pop_frame ()



#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

inline_for_extraction
val crtgo_combine:
     #nLen:bn_len_s
  -> p:lbignum nLen
  -> e:lbignum nLen
  -> m:lbignum nLen
  -> mprod:lbignum nLen
  -> a:lbignum nLen
  -> acc:lbignum nLen
  -> Stack unit
     (requires fun h ->
      live h p /\ live h e /\ live h m /\ live h mprod /\ live h a /\ live h acc /\
      disjoint p acc /\ disjoint e acc /\ disjoint m acc /\ disjoint mprod acc /\ disjoint a acc /\
      isprm (as_snat h p) /\
      as_snat h e > 0 /\
      as_snat h m = exp (as_snat h p) (as_snat h e) /\
      as_snat h mprod > 1 /\
      as_snat h acc > 0 /\
      nat_fits (as_snat h acc + as_snat h mprod * as_snat h m) nLen
      )
     (ensures fun h0 _ h1 ->
      modifies1 acc h0 h1 /\
      as_snat h1 acc = S.crtgo_combine (as_snat h0 p) (as_snat h0 e) (as_snat h0 m)
                                       (as_snat h0 mprod) (as_snat h0 a) (as_snat h0 acc)
      )
let rec crtgo_combine #nLen p e m mprod a acc =
  bn_len_s_fits nLen;
  let h0 = FStar.HyperStack.ST.get () in

  push_frame ();

  let tmp = create nLen (u64 0) in
  bn_remainder mprod m tmp;
  let h2 = FStar.HyperStack.ST.get () in


  let mprodinv = create nLen (u64 0) in
  let h = FStar.HyperStack.ST.get () in
  as_snat_prop h0 m;
  nat_fits_trans (exp (as_snat h p) (as_snat h e)) (as_snat h m) nLen;
  fermat_inv_pe p e tmp mprodinv;

  let y = create nLen (u64 0) in
  bn_modular_sub m a acc tmp;
  bn_modular_mul m mprodinv tmp y;

  let h = FStar.HyperStack.ST.get () in
  multiplication_order_lemma_strict (as_snat h y) (as_snat h m) (as_snat h mprod);
  assert (as_snat h mprod * as_snat h y < as_snat h mprod * as_snat h m);
  nat_fits_trans (as_snat h mprod * as_snat h y)
                 (as_snat h acc + as_snat h mprod * as_snat h m) nLen;
  assert (as_snat h acc + as_snat h mprod * as_snat h y <
          as_snat h acc + as_snat h mprod * as_snat h m);
  nat_fits_trans (as_snat h acc + as_snat h mprod * as_snat h y)
                 (as_snat h acc + as_snat h mprod * as_snat h m) nLen;

  bn_mul_fitting mprod y tmp;
  bn_add_fitting #nLen #nLen acc tmp acc;

//  let h = FStar.HyperStack.ST.get () in
//  assert (as_snat h acc = as_snat h0 acc + as_snat h0 mprod *
//                    ( (
//                       (S.fermat_inv_pe (as_snat h0 p) (as_snat h0 e)
//                                        (as_snat h0 mprod % as_snat h0 m)) *
//                       ((as_snat h0 a - as_snat h0 acc) % as_snat h0 m)
//                       )
//                       % as_snat h0 m));


  pop_frame ()

#reset-options "--z3rlimit 800 --max_fuel 1 --max_ifuel 1"
//#reset-options "--z3rlimit 200"

val crtgo:
     #nLen:bn_len_s
  -> l:size_t{ v l > 0 }
  -> base:factors_list nLen l
  -> values:values_list nLen l
  -> lcur:size_t{v lcur < v l /\ v lcur > 0}
  -> mprod:lbignum nLen
  -> acc:lbignum nLen
  -> Stack unit
     (requires fun h ->
      live h mprod /\ live h acc /\ live h base /\ live h values /\
      disjoint mprod acc /\
      forall_bufel h values (fun a -> live h a /\ disjoint a acc /\ disjoint a mprod) /\
      forall_bufel h base
        (fun (p,e) ->
         live h p /\ live h e /\
         disjoint p e /\
         disjoint p acc /\ disjoint e acc /\
         disjoint p mprod /\ disjoint e mprod /\
         isprm (as_snat h p) /\ as_snat h e > 0) /\
      as_snat h mprod > 1 /\
      as_snat h acc > 0 /\
      factors_list_proper h base /\
      values_list_proper h base values
      )
     (ensures fun h0 _ h1 ->
      modifies2 acc mprod h0 h1
//      as_snat h1 acc =
//        S.crtgo (v l)
//                (as_snat_list_factors #nLen #l h0 base)
//                (as_snat_list_bn #nLen #l h0 values)
//                (v lcur)
//                (as_snat h0 mprod)
//                (as_snat h0 acc)
      )
     (decreases (v l - v lcur))
let rec crtgo #nLen l base values lcur mprod acc =
  let h0 = FStar.HyperStack.ST.get () in
  bn_len_s_fits nLen;
  push_frame ();


  let (p,e) = B.index base lcur in
  assert (let (p',e') = Seq.index (as_snat_list_factors #nLen #l h0 base) (v lcur) in
          as_snat h0 p = p' /\ as_snat h0 e = e');
  let m = create nLen (u64 0) in

  assume (nat_fits (exp (as_snat h0 p) (as_snat h0 e)) nLen);
  bn_exp p e m;

  let a = B.index values lcur in
  assert (let a' = Seq.index (as_snat_list_bn #nLen #l h0 values) (v lcur) in
          as_snat h0 a = a');

//  let h = FStar.HyperStack.ST.get () in
//  as_snat_list_factors_preserves_stack #nLen #l base h0 h;
//  as_snat_list_bn_preserves_stack #nLen #l values h0 h;
//  proper_factor_list_matches_spec h base;
//  proper_values_list_matches_spec h base values;
//  assert (v lcur = v l - 1 ==>
//        (S.crtgo (v l)
//                (as_snat_list_factors #nLen #l h0 base)
//                (as_snat_list_bn #nLen #l h0 values)
//                (v lcur)
//                (as_snat h0 mprod)
//                (as_snat h0 acc) =
//         S.crtgo_combine (as_snat h0 p) (as_snat h0 e) (as_snat h m) (as_snat h0 mprod)
//                         (as_snat h0 a) (as_snat h0 acc))
//                );

  let h1 = FStar.HyperStack.ST.get () in
  as_snat_list_factors_preserves_stack #nLen #l base h0 h1;
  as_snat_list_bn_preserves_stack #nLen #l values h0 h1;
  assume (nat_fits (as_snat h1 acc + as_snat h1 mprod * as_snat h1 m) nLen);
  crtgo_combine p e m mprod a acc;

  let h2 = FStar.HyperStack.ST.get () in
  as_snat_list_factors_preserves_stack #nLen #l base h2 h1;
  as_snat_list_bn_preserves_stack #nLen #l values h2 h1;


  admit ();

  if lcur <>. (l -! 1ul) then begin
    let h = FStar.HyperStack.ST.get () in
    assume (nat_fits (as_snat h mprod * as_snat h m) nLen);
    let tmp = create nLen (u64 0) in
    bn_mul_fitting mprod m tmp;
    copy mprod tmp;
    let h = FStar.HyperStack.ST.get () in
    as_snat_list_factors_preserves_stack #nLen #l base h0 h;
    as_snat_list_bn_preserves_stack #nLen #l values h0 h;

    admit ();
    assume (
      forall_bufel h values (fun a -> live h a /\ disjoint a acc /\ disjoint a mprod) /\
      forall_bufel h base
        (fun (p,e) ->
         live h p /\ live h e /\
         disjoint p e /\ disjoint p acc /\ disjoint e acc /\
         disjoint p mprod /\ disjoint e mprod /\
         isprm (as_snat h p) /\ as_snat h e > 0) /\
      factors_list_proper h base /\
      values_list_proper h base values
      );
    crtgo l base values (lcur +! 1ul) mprod acc
  end;



  admit ();

  pop_frame ()
