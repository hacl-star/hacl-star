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


// max 2^30 bits
type bn_len_s = s:bn_len{v s <= pow2 22}

val bn_len_s_fits: (l:bn_len_s) -> Lemma
  (v l * 64 < max_size_t /\
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
      live h1 n /\ live h1 n2 /\ live h1 g /\ live h1 x /\ live h1 y /\
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
  S.fenu_to_fen2u_lemma #(as_snat h n) (as_snat h y);
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
       live h1 n /\ live h1 n2 /\ live h1 g /\ live h1 r /\ live h1 m /\ live h1 res /\
       modifies1 res h0 h1 /\
       as_snat h1 res =
         S.encrypt_direct #(as_snat h0 n) (as_snat h0 g) (as_snat h0 r) (as_snat h0 m)
    )
let encrypt #n2Len n n2 g r m res = encf n n2 g m r res

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
     live h1 n /\ live h1 u /\
     modifies1 res h0 h1 /\
     as_snat h1 res = S.bigl #(as_snat h0 n) (as_snat h0 u)
     )
let bigl #n2Len n n2 u res = admit() // requires bignum division


type l1_div_l2_cond h (#n2Len:bn_len_s) (p:lbignum n2Len) (q:lbignum n2Len)
                      (n:lbignum n2Len) (n2:lbignum n2Len)
                      (w:lbignum n2Len) (g:lbignum n2Len)
                      (lambda:lbignum n2Len) (l2inv:lbignum n2Len) =
       n_cond h n n2 /\
       (let n = as_snat h n in
        let n2 = as_snat h n2 in
        let g = as_snat h g in
        let lambda = as_snat h lambda in
       (as_snat h p > 1 /\ as_snat h q > 1 /\ n > 1 /\
        isprm (as_snat h p) /\ isprm (as_snat h q) /\
        n = as_snat h p * as_snat h q /\

        as_snat h w < n /\
        as_snat h w < n2 /\ // todo remove

        g < n2 /\
        S.is_g n g /\

        lambda = S.etot (as_snat h p) (as_snat h q) /\
        lambda < n2 /\

        (let x:S.fen2 n = fexp #n2 g lambda in
         assert (isunit #n2 g);
         g_pow_isunit #n2 g lambda;
         isunit_nonzero x;
         as_snat h l2inv = finv0 #n (S.bigl #n x))
        ))


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 0"


val l1_div_l2:
     #n2Len:bn_len_s
  -> p:lbignum n2Len
  -> q:lbignum n2Len
  -> n:lbignum n2Len
  -> n2:lbignum n2Len
  -> w:lbignum n2Len
  -> g:lbignum n2Len
  -> lambda:lbignum n2Len
  -> l2inv:lbignum n2Len
  -> res:lbignum n2Len
  -> Stack unit
    (requires fun h ->
       live h p /\ live h q /\ live h n /\ live h n2 /\
       live h w /\ live h g /\ live h lambda /\ live h l2inv /\ live h res /\
       all_disjoint [loc p; loc q; loc n; loc n2; loc w; loc g; loc l2inv; loc res; loc lambda] /\
       l1_div_l2_cond h p q n n2 w g lambda l2inv
       )
    (ensures fun h0 _ h1 ->
       live h1 p /\ live h1 q /\ live h1 n /\ live h1 w /\
       live h1 g /\ live h1 lambda /\ live h1 l2inv /\
       modifies1 res h0 h1 /\
       as_snat h1 res = S.l1_div_l2 (as_snat h0 p) (as_snat h0 q) (as_snat h0 w) (as_snat h0 g)
    )

let l1_div_l2 #n2Len p q n n2 w g lambda l2inv res =
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
    isunit_nonzero #(as_snat h n2) (fexp #(as_snat h n2) (as_snat h g) (as_snat h lambda));
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
       live h p /\ live h q /\ live h n /\ live h n2 /\
       live h c /\ live h g /\ live h lambda /\ live h l2inv /\ live h res /\
       all_disjoint [loc p; loc q; loc n; loc n2; loc c; loc g; loc l2inv; loc res; loc lambda] /\
       l1_div_l2_cond h p q n n2 c g lambda l2inv
       )
    (ensures fun h0 _ h1 ->
       live h1 p /\ live h1 q /\ live h1 n /\ live h1 c /\
       live h1 g /\ live h1 lambda /\ live h1 l2inv /\
       modifies1 res h0 h1 /\
       as_snat h1 res = S.decrypt_direct (as_snat h0 p) (as_snat h0 q) (as_snat h0 g) (as_snat h0 c)
    )
let decrypt #n2Len p q n n2 g lambda l2inv c res = l1_div_l2 p q n n2 c g lambda l2inv res
