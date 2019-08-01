module Hacl.Impl.HE.DGK

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open FStar.Tactics

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

let crtps_proper (#bnlen:bn_len_s) (#len:ssize_t) (h:mem) (ps:bnlist bnlen len) =
  let ps' = as_snat_bnlist #bnlen #len h ps in
  forall (i:nat{i < Seq.length ps'}).
    Seq.length ps' > 0 /\
    isprm (Seq.index ps' i) /\
    S.is_crtps ps'

let crtes_proper (#bnlen:bn_len_s) (#len:ssize_t) (h:mem) (es:bnlist bnlen len) =
  let es' = as_snat_bnlist #bnlen #len h es in
  forall (i:nat{i < Seq.length es'}).
    Seq.length es' > 0 /\
    Seq.index es' i > 0


let crtas_proper (#bnlen:bn_len_s) (#len:ssize_t) (h:mem)
                 (ps:bnlist bnlen len)
                 (es:bnlist bnlen len)
                 (as:bnlist bnlen len) =
  let ps' = as_snat_bnlist #bnlen #len h ps in
  let es' = as_snat_bnlist #bnlen #len h es in
  let as' = as_snat_bnlist #bnlen #len h as in
  Seq.length ps' = Seq.length es' /\
  Seq.length as' = Seq.length es' /\
  (forall (i:nat{i < Seq.length ps'}).
    let a = Seq.index as' i in
    let p = Seq.index ps' i in
    let e = Seq.index es' i in
    a < exp p e)

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

#reset-options "--z3rlimit 400 --max_fuel 0 --max_ifuel 0"
//#reset-options "--z3rlimit 200"

type crt_constraint
     (#nLen:bn_len_s)
     (#l:ssize_t{ v l > 0 })
     (ps:bnlist nLen l)
     (es:bnlist nLen l)
     (as:bnlist nLen l)
     (acc:lbignum nLen)
     (h:mem) =
      live h acc /\ live h ps /\ live h es /\ live h as /\
      disjoint ps es /\ disjoint es as /\
      disjoint as acc /\ disjoint ps acc /\ disjoint es acc /\
      Seq.length (as_snat_bnlist #nLen #l h ps) = v l /\
      Seq.length (as_snat_bnlist #nLen #l h es) = v l /\
      crtps_proper h ps /\
      crtes_proper h es /\
      crtas_proper h ps es as

type crtgo_constraint
     (#nLen:bn_len_s)
     (#l:ssize_t{ v l > 0 })
     (ps:bnlist nLen l)
     (es:bnlist nLen l)
     (as:bnlist nLen l)
     (mprod:lbignum nLen)
     (acc:lbignum nLen)
     (h:mem) =
      crt_constraint ps es as acc h /\
      live h mprod /\
      disjoint as mprod /\
      disjoint ps mprod /\
      disjoint es mprod /\
      as_snat h mprod > 1

val crtgo_constraint_trans:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 0 }
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> as:bnlist nLen l
  -> mprod:lbignum nLen
  -> acc:lbignum nLen
  -> h0:mem
  -> h1:mem
  -> Lemma
  (requires (live h1 ps /\ live h1 es /\ live h1 as /\ live h1 mprod /\ live h1 acc /\
             crtgo_constraint ps es as mprod acc h0 /\
             as_seq h0 ps == as_seq h1 ps /\
             as_seq h0 es == as_seq h1 es /\
             as_seq h0 as == as_seq h1 as /\
             as_snat h1 mprod > 1
             ))
  (ensures (crtgo_constraint ps es as mprod acc h1))
let crtgo_constraint_trans #nLen #l ps es as mprod acc h0 h1 =
  as_snat_bnlist_preserves_h h0 h1 ps;
  as_snat_bnlist_preserves_h h0 h1 as;
  as_snat_bnlist_preserves_h h0 h1 es


val crtlemma1: nLen:bn_len_s -> acc:nat -> mprod:pos -> p:prm -> e:nat -> Lemma
  (requires (nat_fits (acc + mprod * exp p e) nLen))
  (ensures (nat_fits (exp p e) nLen /\
            nat_fits (mprod * exp p e) nLen))
let crtlemma1 nLen acc mprod p e =
  nat_fits_trans (mprod * exp p e) (acc + mprod * exp p e) nLen;
  nat_fits_trans (exp p e) (mprod * exp p e) nLen

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

// It takes about 5 minutes to verify the memory safety only.
// And in fact doesn't, though it verifies everything
// if admitted in the last line.
val crtgo:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 0 }
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> as:bnlist nLen l
  -> lcur:size_t{v lcur < v l /\ v lcur > 0}
  -> mprod:lbignum nLen
  -> acc:lbignum nLen
  -> Stack unit
     (requires fun h -> crtgo_constraint ps es as mprod acc h)
     (ensures fun h0 _ h1 ->
      modifies2 acc mprod h0 h1 /\
      as_snat h1 acc =
        S.crtgo (v l)
                (as_snat_bnlist h0 ps)
                (as_snat_bnlist h0 es)
                (as_snat_bnlist h0 as)
                (v lcur)
                (as_snat h0 mprod)
                (as_snat h0 acc)
      )
     (decreases (v l - v lcur))
let rec crtgo #nLen #l ps es as lcur mprod acc =
  admit ();
  let h0 = FStar.HyperStack.ST.get () in
  bn_len_s_fits nLen;
  push_frame ();

  let p = bnlist_ix ps lcur in
  let e = bnlist_ix es lcur in
  let a = bnlist_ix as lcur in
  let h = FStar.HyperStack.ST.get () in
  crtgo_constraint_trans ps es as mprod acc h0 h;

  assume (nat_fits (as_snat h acc + as_snat h mprod * exp (as_snat h p) (as_snat h e)) nLen);
  crtlemma1 nLen (as_snat h acc) (as_snat h mprod) (as_snat h p) (as_snat h e);
  let m = create nLen (u64 0) in
  bn_exp p e m;

  let h = FStar.HyperStack.ST.get () in
  crtgo_constraint_trans ps es as mprod acc h0 h;
  crtgo_combine p e m mprod a acc;

  if lcur <>. (l -! 1ul) then begin
    let h = FStar.HyperStack.ST.get () in
    crtgo_constraint_trans ps es as mprod acc h0 h;
    let tmp = create nLen (u64 0) in
    bn_mul_fitting mprod m tmp;
    copy mprod tmp;

    let h = FStar.HyperStack.ST.get () in
    big_times_pos_is_big (as_snat h mprod) (as_snat h m);
    assert (as_snat h mprod > 1);
    crtgo_constraint_trans ps es as mprod acc h0 h;

    crtgo ps es as (lcur +! 1ul) mprod acc
  end;


  pop_frame ()


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val crt:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 1 }
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> as:bnlist nLen l
  -> acc:lbignum nLen
  -> Stack unit
     (requires fun h -> crt_constraint ps es as acc h)
     (ensures fun h0 _ h1 ->
      modifies1 acc h0 h1 /\
      as_snat h1 acc =
        S.crt (v l)
              (as_snat_bnlist h0 ps)
              (as_snat_bnlist h0 es)
              (as_snat_bnlist h0 as)
      )
let rec crt #nLen #l ps es as acc =
  bn_len_s_fits nLen;
  let h0 = FStar.HyperStack.ST.get () in
  push_frame ();

  let p = bnlist_ix ps 0ul in
  let e = bnlist_ix es 0ul in
  let a = bnlist_ix as 0ul in

  let mprod = create nLen (u64 0) in
  let h = FStar.HyperStack.ST.get () in
  assume (nat_fits (exp (as_snat h p) (as_snat h e)) nLen);
  bn_exp p e mprod;
  copy acc a;

  let h = FStar.HyperStack.ST.get () in
  as_snat_bnlist_preserves_h h0 h ps;
  as_snat_bnlist_preserves_h h0 h as;
  as_snat_bnlist_preserves_h h0 h es;

  assert (live h mprod);
  assert (as_snat h mprod > 1);
  assert (disjoint as mprod /\
      disjoint ps mprod /\
      disjoint es mprod);

  crtgo ps es as 1ul mprod acc;

  pop_frame ()


#reset-options "--z3rlimit 800 --max_fuel 1 --max_ifuel 0"

val tailprod_go:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 1 }
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> i:size_t{v i > 0 /\ v i <= v l}
  -> j:size_t{v j <= v i}
  -> m:lbignum nLen
  -> Stack unit
  (requires fun h ->
      live h m /\ live h ps /\ live h es /\
      disjoint ps es /\ disjoint ps m /\ disjoint es m /\
      Seq.length (as_snat_bnlist #nLen #l h ps) = v l /\
      Seq.length (as_snat_bnlist #nLen #l h es) = v l /\
      crtps_proper h ps /\
      crtes_proper h es /\
      as_snat h m > 1
      )
  (ensures fun h0 _ h1 ->
   modifies1 m h0 h1 /\
   as_snat h1 m =
   S.tailprod_go (as_snat_bnlist h0 ps)
                 (as_snat_bnlist h0 es)
                 (v i)
                 (v j)
                 (as_snat h0 m)
   )
  (decreases (v i - v j))
let rec tailprod_go #nLen #l ps es i j m =
  admit ();
  if j =. i then () else begin
    let h0 = FStar.HyperStack.ST.get () in
    bn_len_s_fits nLen;
    push_frame ();

    let p = bnlist_ix ps 0ul in
    let e = bnlist_ix es 0ul in

    let tmp1 = create nLen (u64 0) in
    let tmp2 = create nLen (u64 0) in
    let h = FStar.HyperStack.ST.get () in
    assume (nat_fits (as_snat h m * exp (as_snat h p) (as_snat h e)) nLen);
    assume (nat_fits (exp (as_snat h p) (as_snat h e)) nLen);
    bn_exp p e tmp1;
    bn_mul_fitting m tmp1 tmp2;
    copy m tmp2;

    let h = FStar.HyperStack.ST.get () in
    as_snat_bnlist_preserves_h h0 h ps;
    as_snat_bnlist_preserves_h h0 h es;

    tailprod_go ps es i (j +! 1ul) tmp2;

    pop_frame ()
  end

val tailprod:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 1 }
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> i:size_t{v i > 0 /\ v i <= v l}
  -> m:lbignum nLen
  -> Stack unit
  (requires fun h ->
      live h m /\ live h ps /\ live h es /\
      disjoint ps es /\ disjoint ps m /\ disjoint es m /\
      Seq.length (as_snat_bnlist #nLen #l h ps) = v l /\
      Seq.length (as_snat_bnlist #nLen #l h es) = v l /\
      crtps_proper h ps /\
      crtes_proper h es
      )
  (ensures fun h0 _ h1 ->
   modifies1 m h0 h1 /\
   as_snat h1 m =
   S.tailprod (as_snat_bnlist h0 ps)
              (as_snat_bnlist h0 es)
              (v i)
   )
let tailprod #nLen #l ps es i m =
  admit ();
  push_frame ();

  let p = bnlist_ix ps 0ul in
  let e = bnlist_ix es 0ul in
  bn_exp p e m;

  tailprod_go ps es i 1ul m;

  pop_frame ()

val fullprod:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 1 }
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> m:lbignum nLen
  -> Stack unit
  (requires fun h ->
      live h m /\ live h ps /\ live h es /\
      disjoint ps es /\ disjoint ps m /\ disjoint es m /\
      Seq.length (as_snat_bnlist #nLen #l h ps) = v l /\
      Seq.length (as_snat_bnlist #nLen #l h es) = v l /\
      crtps_proper h ps /\
      crtes_proper h es
      )
  (ensures fun h0 _ h1 ->
   modifies1 m h0 h1 /\
   as_snat h1 m =
   S.fullprod (as_snat_bnlist h0 ps) (as_snat_bnlist h0 es))
let fullprod #nLen #l ps es m = tailprod ps es l m


val solve_dlp_single:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> p:lbignum nLen
  -> e:lbignum nLen
  -> g:lbignum nLen
  -> a:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
  (requires fun h ->
      live h n /\ live h p /\ live h e /\ live h g /\ live h a /\ live h res /\
      all_disjoint [loc n; loc p; loc e; loc g; loc a; loc res] /\
      exp (as_snat h p) (as_snat h e) < as_snat h n /\
      as_snat h g < as_snat h n /\
      as_snat h a < as_snat h n
      )
  (ensures fun h0 _ h1 -> modifies1 res h0 h1)
let solve_dlp_single #nLen n p e g a res =
  admit ();

  push_frame ();

  let one:lbignum 1ul = bn_one #1ul in
  let tmp:lbignum 1ul = bn_one #nLen in

  let p_e = create nLen (u64 0) in
  bn_exp p e p_e;

  let exp_try = create nLen (u64 1) in
  let current_g = bn_copy g in

  let whilecond () = begin
     let b1 = bn_is_leq exp_try p_e in
     let b2 = bn_is_equal current_g a in
     b1 && b2
  end in

  Lib.Loops.while (fun _ -> true) (fun _ -> true) whilecond (fun _ ->
    bn_add_fitting exp_try one exp_try;
    bn_modular_mul n current_g g tmp;
    copy g tmp);

  pop_frame ()

val pohlig_hellman:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 1 }
  -> n:lbignum nLen
  -> ps:bnlist nLen l
  -> es:bnlist nLen l
  -> g:lbignum nLen
  -> a:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
  (requires fun h ->
      live h g /\ live h a /\ live h ps /\ live h es /\
      disjoint ps es /\
      disjoint ps g /\ disjoint es g /\
      disjoint ps a /\ disjoint es a /\
      Seq.length (as_snat_bnlist #nLen #l h ps) = v l /\
      Seq.length (as_snat_bnlist #nLen #l h es) = v l /\
      as_snat h g < as_snat h n /\
      as_snat h a < as_snat h n /\
      //iscomp (as_snat h n) /\
      // g is unit and its mult order is prod p^e
      crtps_proper h ps /\
      crtes_proper h es
      )
  (ensures fun h0 _ h1 ->
     modifies1 res h0 h1
//     as_snat h1 res = S.solve_dlp #(as_snat h0 n)
//                                  (as_snat_bnlist #nLen #l h0 ps)
//                                  (as_snat_bnlist #nLen #l h0 ps)
//                                  (as_snat h0 g)
//                                  (as_snat h0 a)
     )
let pohlig_hellman #nLen #l n ps es g a res =
  admit ();
  push_frame ();

  let u = create nLen (u64 0) in
  fullprod ps es u;

  let as = create (nLen *! l) (u64 0) in
  let p_e = create nLen (u64 0) in
  let pow = create nLen (u64 0) in
  let div_r = create nLen (u64 0) in
  let gi = create nLen (u64 0) in
  let ai = create nLen (u64 0) in

  Lib.Loops.for 0ul (l -! 1) (fun _ _ -> True) (fun i ->
    let curA = sub as (i *! nLen) nLen in

    let p = bnlist_ix ps 0ul in
    let e = bnlist_ix es 0ul in
    bn_exp p e p_e;

    bn_divide u p_e pow div_r;

    bn_modular_exp n g pow gi;
    bn_modular_exp n a pow ai;

    solve_dlp_single n p e gi ai curA
  );

  crt ps es as res;

  pop_frame ()
