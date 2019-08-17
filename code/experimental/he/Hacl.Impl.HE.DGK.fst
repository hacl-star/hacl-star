// Also see DGK.Extra for the unsafe decryption
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
open Hacl.Impl.Bignum.Openssl
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

type proper_secret
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

type secret_mem
  (hp:mem)
  (#nLen:bn_len_s)
  (p:lbignum nLen)
  (q:lbignum nLen)
  (n:lbignum nLen)
  (u:lbignum nLen)
  (v:lbignum nLen)
  (g:lbignum nLen)
  (h:lbignum nLen) =
    live hp p /\
    live hp q /\
    live hp n /\
    live hp u /\
    live hp v /\
    live hp g /\
    live hp h /\
    all_disjoint [loc p; loc q; loc n; loc u; loc v; loc g; loc h]

val as_spec_sk:
     hp:mem
  -> #nLen:bn_len_s
  -> p:lbignum nLen
  -> q:lbignum nLen
  -> n:lbignum nLen
  -> u:lbignum nLen
  -> v:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen{proper_secret hp p q n u v g h}
  -> GTot (s':S.secret)
let as_spec_sk hp #nLen p q n u v g h =
  S.Secret (as_snat hp p)
           (as_snat hp q)
           (as_snat hp u)
           (as_snat hp v)
           (as_snat hp g)
           (as_snat hp h)


type proper_public
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

type public_mem
  (hp:mem)
  (#nLen:bn_len_s)
  (n:lbignum nLen)
  (u:lbignum nLen)
  (g:lbignum nLen)
  (h:lbignum nLen) =
    live hp n /\
    live hp u /\
    live hp g /\
    live hp h /\
    all_disjoint [loc n; loc u; loc g; loc h]

val as_spec_pk:
     hp:mem
  -> #nLen:bn_len_s
  -> n:lbignum nLen
  -> u:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen{proper_public hp n u g h}
  -> GTot (p':S.public)
let as_spec_pk hp #nLen n u g h =
  S.Public (as_snat hp n)
           (as_snat hp u)
           (as_snat hp g)
           (as_snat hp h)

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val encrypt:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> u:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen
  -> r:lbignum nLen
  -> m:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
     (requires fun hp ->
      proper_public hp n u g h /\ public_mem hp n u g h /\
      as_snat hp r > 1 /\
      as_snat hp m < as_snat hp u /\
      live hp r /\ live hp m /\ live hp res /\
      disjoint m g /\
      disjoint h r /\
      disjoint n res)
     (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res = S.encrypt (as_spec_pk h0 n u g h) (as_snat h0 r) (as_snat h0 m)
      )
let encrypt #nLen n u g h r m res =
  bn_len_s_fits nLen;

  push_frame ();
  let hp0 = FStar.HyperStack.ST.get () in

  let tmp1 = create nLen (u64 0) in
  let tmp2 = create nLen (u64 0) in

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
  -> p:lbignum nLen
  -> q:lbignum nLen
  -> n:lbignum nLen
  -> u:lbignum nLen
  -> v:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen
  -> c:lbignum nLen
  -> Stack bool
     (requires fun hp ->
      proper_secret hp p q n u v g h /\
      secret_mem hp p q n u v g h /\
      as_snat hp c < as_snat hp u /\
      live hp c /\
      disjoint v c)
     (ensures fun h0 b h1 ->
      modifies0 h0 h1 /\
      b = S.check_is_zero (as_spec_sk h0 p q n u v g h) (as_snat h0 c)
      )
let check_is_zero #nLen p q n u v g h c =
  bn_len_s_fits nLen;
  push_frame ();
  let hp0 = FStar.HyperStack.ST.get () in

  let tmp = create nLen (u64 0) in
  to_fe_idemp #(as_snat hp0 n) (as_snat hp0 c);
  bn_modular_exp n c v tmp;

  let one:lbignum 1ul = bn_one #1ul in

  let b = bn_is_equal tmp one in

  pop_frame ();
  b

val hom_add:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> c1:lbignum nLen
  -> c2:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
     (requires fun hp ->
      live hp n /\ live hp c1 /\ live hp c2 /\ live hp res /\
      disjoint c1 res /\ disjoint c2 res /\ disjoint n res /\
      as_snat hp c1 < as_snat hp n /\
      as_snat hp c2 < as_snat hp n /\
      as_snat hp n > 1 /\ iscomp (as_snat hp n)
      )
     (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\

      as_snat h1 res = S.hom_add #(as_snat h0 n) (as_snat h0 c1) (as_snat h0 c2)
      )
let hom_add #nLen n c1 c2 res =
  bn_len_s_fits nLen;
  bn_modular_mul n c1 c2 res

val hom_mul_plain:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> c:lbignum nLen
  -> k:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
     (requires fun h ->
       live h n /\ live h c /\ live h k /\ live h res /\
       all_disjoint [loc n; loc c; loc k; loc res] /\
       as_snat h n > 1 /\
       iscomp (as_snat h n) /\
       as_snat h c < as_snat h n /\
       as_snat h k < as_snat h n)
     (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res = S.hom_mul_plain #(as_snat h0 n) (as_snat h0 c) (as_snat h0 k))
let hom_mul_plain #nLen n c k res =
  bn_len_s_fits nLen;
  bn_modular_exp n c k res
