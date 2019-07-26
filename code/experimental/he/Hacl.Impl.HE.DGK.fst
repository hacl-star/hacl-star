module Hacl.Impl.HE.DGK

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Math.Algebra

open Hacl.Impl.Bignum

module S = Hacl.Spec.HE.DGK


type bn_len_s = s:bn_len{v s <= pow2 22}

val bn_len_s_fits: (l:bn_len_s) -> Lemma
  (
   v l * 2 < max_size_t /\
   v l * 64 < max_size_t /\
   v l * 128 < max_size_t /\
   (v l + 1) < max_size_t
  )
let bn_len_s_fits _ = ()

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

         u > 1 /\ divides u (p-1) /\ divides u (q-1) /\
         v > 1 /\ divides v (p-1) /\ divides v (q-1) /\

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
        (u > 1 /\ g < n /\ h < n /\ isunit #n g /\ isunit #n h))

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
let as_spec_pk #nLen hp s =
  S.Public (as_snat hp (Pub?.n s))
           (as_snat hp (Pub?.u s))
           (as_snat hp (Pub?.g s))
           (as_snat hp (Pub?.h s))

val s2p: #nLen:bn_len_s -> s:secret nLen ->
  Stack (public nLen)
        (requires fun h -> proper_secret h s /\ secret_mem h s)
        (ensures fun h0 p h1 ->
         h0 == h1 /\
         proper_public h1 p /\
         public_mem h1 p /\
         as_spec_pk h1 p = S.s2p (as_spec_sk h0 s))
let s2p #nLen s = Pub (Sec?.n s) (Sec?.u s) (Sec?.g s) (Sec?.h s)
