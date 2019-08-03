module Hacl.Impl.HE.Paillier

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Math.Algebra

open Hacl.Impl.Bignum

module S = Hacl.Spec.HE.Paillier
module A = Lib.Math.Algebra
module B = LowStar.Buffer


// max 2^30 bits
type bn_len_s = s:bn_len{v s <= pow2 22}

val bn_len_s_fits: (l:bn_len_s) -> Lemma
  (
   v l * 2 < max_size_t /\
   v l * 64 < max_size_t /\
   v l * 128 < max_size_t /\
   (v l + 1) < max_size_t
  )
let bn_len_s_fits _ = ()




#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 0"

type n_cond h (#n2Len:bn_len_s) (n:lbignum n2Len) (n2:lbignum n2Len) =
       as_snat h n > 1 /\
       as_snat h n2 > 1 /\
       iscomp (as_snat h n) /\
       as_snat h n * as_snat h n = as_snat h n2 /\
       as_snat h n < as_snat h n2


type encf_cond h (#n2Len:bn_len_s) (n:lbignum n2Len) (n2:lbignum n2Len)
                (g:lbignum n2Len) (x:lbignum n2Len) (y:lbignum n2Len) =
       n_cond h n n2 /\

       as_snat h g < as_snat h n2 /\
       S.is_g (as_snat h n) (as_snat h g) /\

       as_snat h x < as_snat h n /\

       as_snat h y < as_snat h n /\
       isunit #(as_snat h n) (as_snat h y)

noextract inline_for_extraction
val encf:
     #n2Len:bn_len_s
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> g:lbignum n2Len
  -> x:lbignum n2Len
  -> y:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h n2 /\ live h g /\ live h x /\ live h y /\ live h res /\
       all_disjoint [loc n; loc n2; loc g; loc x; loc y; loc res] /\
       encf_cond h n n2 g x y
       )
    (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      (as_snat h1 res = S.encf #(as_snat h0 n) (as_snat h0 g) (as_snat h0 x) (as_snat h0 y))
      )
let encf #n2Len n n2 g x y res =
  bn_len_s_fits n2Len;
  push_frame();
  let tmp1:lbignum n2Len = create n2Len (uint 0) in
  let tmp2:lbignum n2Len = create n2Len (uint 0) in
  bn_modular_exp n2 g x tmp1;
  bn_modular_exp n2 y n tmp2;
  bn_modular_mul n2 tmp1 tmp2 res;

  let h = FStar.HyperStack.ST.get () in
  to_fe_idemp #(as_snat h n2) (as_snat h g);
  to_fe_idemp #(as_snat h n2) (as_snat h y);

  pop_frame ()

val encrypt:
     #n2Len:bn_len_s
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> g:lbignum n2Len
  -> r:lbignum n2Len
  -> m:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h n2 /\ live h g /\ live h r /\ live h m /\ live h res /\
       all_disjoint [loc n; loc n2; loc g; loc r; loc m; loc res] /\
       encf_cond h n n2 g m r
       )
    (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res =
         S.encrypt_direct #(as_snat h0 n) (as_snat h0 g) (as_snat h0 r) (as_snat h0 m)
    )
let encrypt #n2Len n n2 g r m res = encf n n2 g m r res

noextract inline_for_extraction
val bigl:
     #n2Len:bn_len_s
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> u:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
    (requires fun h ->
     live h n /\ live h u /\ live h res /\
     all_disjoint [loc n; loc n2; loc u; loc res] /\
     n_cond h n n2 /\
     as_snat h u > 0 /\ as_snat h u < as_snat h n2)
    (ensures fun h0 _ h1 ->
     modifies1 res h0 h1 /\
     as_snat h1 res = S.bigl #(as_snat h0 n) (as_snat h0 u)
     )
let bigl #n2Len n n2 u res =
  assert_norm (issnat 1);
  push_frame ();
  let one:lbignum 1ul = nat_to_bignum_exact 1 in
  let tmp = create n2Len (uint 0) in
  let _rem = create n2Len (uint 0) in

  let _ = bn_sub_exact u one tmp in
  bn_divide tmp n res _rem;

  pop_frame ()


#reset-options "--z3rlimit 200 --max_fuel 2 --max_ifuel 0"

//noeq
//type secret (n2Len:bn_len_s) = {
//    p:lbignum n2Len
//  ; q:lbignum n2Len
//  ; n:lbignum n2Len
//  ; n2:lbignum n2Len
//  ; g:lbignum n2Len
//  ; lambda:lbignum n2Len
//  ; l2inv:lbignum n2Len }


type proper_secret h
     (#n2Len:bn_len_s)
     (p:lbignum n2Len)
     (q:lbignum n2Len)
     (n:lbignum n2Len)
     (n2:lbignum n2Len)
     (g:lbignum n2Len)
     (lambda:lbignum n2Len)
     (l2inv:lbignum n2Len) =
       n_cond h n n2 /\
       (let n = as_snat h n in
        let n2 = as_snat h n2 in
        let p = as_snat h p in
        let q = as_snat h q in
        let g = as_snat h g in
        let lambda = as_snat h lambda in
       (p > 1 /\ q > 1 /\ p <> q /\ n > 1 /\
        isprm p /\ isprm q /\ n = p * q /\

        g < n2 /\
        S.is_g n g /\

        lambda = carm_pq p q /\
        lambda < n2 /\

        // This can be actually proven inplace, but it works slower then
        mexp #n2 g lambda > 0 /\
        as_snat h l2inv = S.fermat_inv_pq p q (S.bigl #n (mexp #n2 g lambda))))

type secret_mem h
     (#n2Len:bn_len_s)
     (p:lbignum n2Len)
     (q:lbignum n2Len)
     (n:lbignum n2Len)
     (n2:lbignum n2Len)
     (g:lbignum n2Len)
     (lambda:lbignum n2Len)
     (l2inv:lbignum n2Len) =
  live h p /\
  live h q /\
  live h n /\
  live h n2 /\
  live h g /\
  live h lambda /\
  live h l2inv /\
  all_disjoint [loc p; loc q; loc n;
                loc n2; loc g; loc lambda;
                loc l2inv]

type secret_disjoint_with h
     (#n2Len:bn_len_s)
     (p:lbignum n2Len)
     (q:lbignum n2Len)
     (n:lbignum n2Len)
     (n2:lbignum n2Len)
     (g:lbignum n2Len)
     (lambda:lbignum n2Len)
     (l2inv:lbignum n2Len)
     (a:lbignum n2Len) =
  disjoint p a /\
  disjoint q a /\
  disjoint n a /\
  disjoint n2 a /\
  disjoint g a /\
  disjoint lambda a /\
  disjoint l2inv a

val mul_order_lemma2: a:pos -> b:pos -> c:pos -> d:pos -> Lemma
  (requires (a >= c /\ b >= d))
  (ensures (a * b >= c * d))
let mul_order_lemma2 a b c d =
  Math.Lemmas.multiplication_order_lemma a c b;
  Math.Lemmas.multiplication_order_lemma b d a

val mul_order_lemma3: a:pos -> b:pos -> c:pos -> d:pos -> Lemma
  (requires (a <= c /\ b <= d))
  (ensures (a * b <= c * d))
let mul_order_lemma3 a b c d = mul_order_lemma2 c d a b

val mul_order_lemma4: p:pos -> q:pos -> Lemma
  (p <= p * q && q <= p * q)
let mul_order_lemma4 p q = ()

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

noextract inline_for_extraction
val carm:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
     (requires fun h ->
      live h p /\ live h q /\ live h n /\ live h n2 /\ live h res /\
      all_disjoint [loc p; loc q; loc n; loc n2; loc res] /\
      isprm (as_snat h p) /\
      isprm (as_snat h q) /\
      as_snat h p <> as_snat h q /\
      as_snat h p * as_snat h q = as_snat h n /\
      as_snat h n * as_snat h n = as_snat h n2 /\
      as_snat h n > 1)
     (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res = carm_pq (as_snat h0 p) (as_snat h0 q))
let carm #n2Len p q n n2 res =
  bn_len_s_fits n2Len;

  push_frame ();

  let p' = bn_copy p in
  let q' = bn_copy q in

  let one:lbignum 1ul = bn_one #1ul in

  bn_sub_exact p' one p';
  bn_sub_exact q' one q';

  let h = FStar.HyperStack.ST.get () in
  as_snat_prop #n2Len h n;
  as_snat_prop #n2Len h n2;
  assert (as_snat h p - 1 < as_snat h n);
  assert (as_snat h q - 1 < as_snat h n);

  mul_order_lemma3 (as_snat h p - 1) (as_snat h q - 1) (as_snat h n) (as_snat h n);
  snat_order ((as_snat h p - 1) * (as_snat h q - 1)) (as_snat h n2);
  assert (issnat (as_snat h p' * as_snat h q'));

  nat_bytes_num_fit ((as_snat h p - 1) * (as_snat h q - 1)) (as_snat h n2);
  assert (v (nat_bytes_num (as_snat h p' * as_snat h q')) <= v n2Len);

  bn_lcm p' q' res;

  pop_frame ()


noextract inline_for_extraction
val fermat_inverse:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> a:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
     (requires fun h ->
      live h p /\ live h q /\ live h n /\ live h n2 /\ live h a /\ live h res /\
      all_disjoint [loc p; loc q; loc n; loc n2; loc a; loc res] /\
      isprm (as_snat h p) /\
      isprm (as_snat h q) /\
      as_snat h p <> as_snat h q /\
      as_snat h p * as_snat h q = as_snat h n /\
      as_snat h n * as_snat h n = as_snat h n2 /\
      as_snat h n > 1 /\
      as_snat h a < as_snat h n)
     (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res =
      S.fermat_inv_pq (as_snat h1 p) (as_snat h1 q) (as_snat h1 a))
let fermat_inverse #n2Len p q n n2 a res =
  bn_len_s_fits n2Len;

  push_frame ();

  let bn_carm = create n2Len (u64 0) in
  carm p q n n2 bn_carm;

  let one = bn_one #1ul in
  bn_sub_exact bn_carm one bn_carm;

  let h = FStar.HyperStack.ST.get () in
  Math.Lemmas.multiplication_order_lemma (as_snat h n) 1 (as_snat h n) ;
  to_fe_idemp #(as_snat h n) (as_snat h a);
  bn_modular_exp n a bn_carm res;

  let h = FStar.HyperStack.ST.get () in
  assert (as_snat h bn_carm = carm_pq (as_snat h p) (as_snat h q) - 1);
  assert (as_snat h res = mexp #(as_snat h n) (as_snat h a)
                               (carm_pq (as_snat h p) (as_snat h q) - 1));

  pop_frame ()


#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

val to_secret:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> g:lbignum n2Len
  -> lambda:lbignum n2Len
  -> l2inv: lbignum n2Len
  -> Stack unit
     (requires fun h ->
      live h p /\ live h q /\ live h n /\ live h n2 /\ live h g /\ live h lambda /\ live h l2inv /\
      all_disjoint [loc p; loc q; loc n; loc n2; loc g; loc lambda; loc l2inv] /\
      isprm (as_snat h p) /\
      isprm (as_snat h q) /\
      as_snat h p <> as_snat h q /\
      as_snat h p * as_snat h q = as_snat h n /\
      as_snat h n * as_snat h n = as_snat h n2 /\
      as_snat h n > 1 /\
      as_snat h g < as_snat h n2 /\
      S.is_g (as_snat h n) (as_snat h g))
     (ensures fun h0 _ h1 ->
      live h1 p /\ live h1 q /\ live h1 n /\ live h1 n2 /\ live h1 g /\

      secret_mem h1 p q n n2 g lambda l2inv /\
      proper_secret h1 p q n n2 g lambda l2inv
      )
let to_secret #n2Len p q n n2 g lambda l2inv =
  bn_len_s_fits n2Len;

  push_frame ();

  carm p q n n2 lambda;

  let h = FStar.HyperStack.ST.get () in
  to_fe_idemp #(as_snat h n2) (as_snat h g);
  bn_modular_exp n2 g lambda l2inv;

  let h = FStar.HyperStack.ST.get () in
  assert (isunit #(as_snat h n2) (as_snat h g));
  g_pow_isunit #(as_snat h n2) (as_snat h g) (as_snat h lambda);
  isunit_nonzero #(as_snat h n2) (as_snat h l2inv);

  // TODO this variable is temporary.
  // Putting push_frame before this call and pop_frame right
  // after the last one doesn't work for some reason.
  let bl_inv:lbignum n2Len = create n2Len (uint 0) in
  bigl n n2 l2inv bl_inv;

  let h = FStar.HyperStack.ST.get () in
  assert (as_snat h bl_inv =
           S.bigl #(as_snat h n)
                   (mexp #(as_snat h n2) (as_snat h g) (as_snat h lambda)));

  assert (as_snat h bl_inv < as_snat h n);

  fermat_inverse p q n n2 bl_inv l2inv;
  pop_frame ()

noextract inline_for_extraction
val l1_div_l2:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> g:lbignum n2Len
  -> lambda:lbignum n2Len
  -> l2inv:lbignum n2Len
  -> w:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
    (requires fun h ->
       secret_mem h p q n n2 g lambda l2inv /\ live h w /\ live h res /\
       secret_disjoint_with h p q n n2 g lambda l2inv w /\
       secret_disjoint_with h p q n n2 g lambda l2inv res /\
       disjoint w res /\

       proper_secret h p q n n2 g lambda l2inv /\
       as_snat h w < as_snat h n2)
    (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res =
       S.l1_div_l2 (as_snat h0 p) (as_snat h0 q)
                   (as_snat h0 w) (as_snat h0 g))

let l1_div_l2 #n2Len p q n n2 g lambda l2inv w res =

  bn_len_s_fits n2Len;

  let h = FStar.HyperStack.ST.get () in
  to_fe_idemp #(as_snat h n2) (as_snat h w);
  bn_modular_exp n2 w lambda res;

  if bn_is_zero res then begin
    let h = FStar.HyperStack.ST.get () in
    assert (S.l1_div_l2 (as_snat h p) (as_snat h q) (as_snat h w) (as_snat h g) = as_snat h res)
  end else begin
    let h = FStar.HyperStack.ST.get () in
    g_pow_isunit #(as_snat h n2) (as_snat h g) (as_snat h lambda);
    isunit_nonzero #(as_snat h n2) (mexp #(as_snat h n2) (as_snat h g) (as_snat h lambda));
    assert (S.l1_div_l2 (as_snat h p) (as_snat h q) (as_snat h w) (as_snat h g) =
            ( *% ) #(as_snat h n)
              (S.bigl #(as_snat h n) (as_snat h res))
              (as_snat h l2inv));

    push_frame ();
    let l1:lbignum n2Len = create n2Len (uint 0) in
    bigl n n2 res l1;
    bn_modular_mul n l1 l2inv res;


    let h1 = FStar.HyperStack.ST.get () in

    assert (as_snat h1 l1 = S.bigl #(as_snat h n) (as_snat h res));
    assert (as_snat h1 res =
              (S.bigl #(as_snat h n) (as_snat h res) * as_snat h l2inv) % as_snat h n);
    assert (as_snat h1 res =
              ( *% ) #(as_snat h n) (S.bigl #(as_snat h n) (as_snat h res)) (as_snat h l2inv));

    pop_frame ()
  end

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val decrypt:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> g:lbignum n2Len
  -> lambda:lbignum n2Len
  -> l2inv:lbignum n2Len
  -> c:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
    (requires fun h ->
       secret_mem h p q n n2 g lambda l2inv /\
       live h c /\ live h res /\
       secret_disjoint_with h p q n n2 g lambda l2inv c /\
       secret_disjoint_with h p q n n2 g lambda l2inv res /\
       disjoint c res /\

       proper_secret h p q n n2 g lambda l2inv /\
       as_snat h c < as_snat h n
       )
    (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res =
         S.decrypt_direct (as_snat h0 p)
           (as_snat h0 q) (as_snat h0 g) (as_snat h0 c)
    )
let decrypt #n2Len p q n n2 g lambda l2inv c res = l1_div_l2 p q n n2 g lambda l2inv c res

val hom_add:
     #n2Len:bn_len_s
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> c1:lbignum n2Len
  -> c2:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
     (requires fun h ->
       live h n /\ live h n2 /\ live h c1 /\ live h c2 /\ live h res /\
       all_disjoint [loc n; loc n2; loc c1; loc c2; loc res] /\
       as_snat h n > 1 /\
       iscomp (as_snat h n) /\
       as_snat h n2 = as_snat h n * as_snat h n /\
       as_snat h c1 < as_snat h n2 /\
       as_snat h c2 < as_snat h n2)
     (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res = S.hom_add #(as_snat h0 n) (as_snat h0 c1) (as_snat h0 c2))
let hom_add #n2Len _ n2 c1 c2 res =
  bn_len_s_fits n2Len;
  bn_modular_mul n2 c1 c2 res

val hom_mul_plain:
     #n2Len:bn_len_s
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> c:lbignum n2Len
  -> k:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
     (requires fun h ->
       live h n /\ live h n2 /\ live h c /\ live h k /\ live h res /\
       all_disjoint [loc n; loc n2; loc c; loc k; loc res] /\
       as_snat h n > 1 /\
       iscomp (as_snat h n) /\
       as_snat h n2 = as_snat h n * as_snat h n /\
       as_snat h c < as_snat h n2 /\
       as_snat h k < as_snat h n)
     (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res = S.hom_mul_plain #(as_snat h0 n) (as_snat h0 c) (as_snat h0 k))
let hom_mul_plain #n2Len _ n2 c k res =
  bn_len_s_fits n2Len;
  bn_modular_exp n2 c k res
