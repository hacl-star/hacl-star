// Unsafe decryption-related parts of DGK
module Hacl.Impl.HE.DGK.Extra

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
open Hacl.Impl.HE.DGK

module S = Hacl.Spec.HE.DGK
//module Seq = Lib.Sequence
module Seq = FStar.Seq
module Seq' = FStar.Monotonic.Seq
module B = Lib.Buffer


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

noextract inline_for_extraction
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

noextract inline_for_extraction
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
    push_frame ();
    let tmp = create nLen (u64 0) in
    bn_mul_fitting mprod m tmp;
    copy mprod tmp;
    pop_frame ();

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

    let p = bnlist_ix ps j in
    let e = bnlist_ix es j in

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

    tailprod_go ps es i (j +! 1ul) m;

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
     #nLen:bn_len_s {v nLen * 128 < max_size_t}
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
  if enable_ossl then solve_dlp_single_external n p e g a res else begin

    push_frame ();

    let one:lbignum 1ul = bn_one #1ul in
    let tmp = create nLen (u64 0) in

    admit ();

    let p_e = create nLen (u64 0) in
    bn_exp p e p_e;

    bn_assign_uint64 res (u64 0);
    let current_g = bn_one #nLen in

    let boolvar = create 1ul 0uy in

    let b_init = bn_is_equal current_g a in
    if b_init then boolvar.(0ul) <- 1uy;

    let test () = boolvar.(0ul) =. 0uy in

    Lib.Loops.while (fun _ -> true) (fun _ -> true) test (fun _ ->
      bn_add_fitting res one res;
      bn_modular_mul n current_g g tmp;
      copy current_g tmp;

      let b1 = bn_is_geq res p_e in
      let b2 = bn_is_equal current_g a in
      if b1 || b2 then boolvar.(0ul) <- 1uy

      );

    pop_frame ()
  end

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

  if l =. 1ul then begin
    push_frame ();
    let p = bnlist_ix ps 0ul in
    let e = bnlist_ix es 0ul in
    solve_dlp_single n p e g a res;
    pop_frame ()
  end else begin
    push_frame ();
    let u = create nLen (u64 0) in
    fullprod ps es u;

    let as = create (nLen *! l) (u64 0) in
    let p_e = create nLen (u64 0) in
    let pow = create nLen (u64 0) in
    let div_r = create nLen (u64 0) in
    let gi = create nLen (u64 0) in
    let ai = create nLen (u64 0) in

    Lib.Loops.for 0ul l (fun _ _ -> True) (fun i ->
      let curA = sub as (i *! nLen) nLen in

      let p = bnlist_ix ps i in
      let e = bnlist_ix es i in
      bn_exp p e p_e;

      bn_divide u p_e pow div_r;

      bn_modular_exp n g pow gi;
      bn_modular_exp n a pow ai;

      solve_dlp_single n p e gi ai curA
    );

    crt ps es as res;
    pop_frame ()
  end

val decrypt:
     #nLen:bn_len_s
  -> #l:ssize_t{ v l > 1 }
  -> p:lbignum nLen
  -> q:lbignum nLen
  -> n:lbignum nLen
  -> u:lbignum nLen
  -> u_ps:bnlist nLen l
  -> u_es:bnlist nLen l
  -> sec_v:lbignum nLen
  -> g:lbignum nLen
  -> h:lbignum nLen
  -> c:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
  (requires fun hp ->
      live hp c /\ live hp res /\ live hp u_ps /\ live hp u_es /\

      disjoint u_ps u_es /\

      proper_secret hp p q n u sec_v g h /\
      secret_mem hp p q n u sec_v g h /\

      as_snat hp c < as_snat hp n /\

      Seq.length (as_snat_bnlist hp u_ps) = v l /\
      Seq.length (as_snat_bnlist hp u_es) = v l /\
      crtps_proper hp u_ps /\
      crtes_proper hp u_es /\
      S.fullprod (as_snat_bnlist #nLen #l hp u_ps)
                 (as_snat_bnlist #nLen #l hp u_es) = as_snat hp u
      )
  (ensures fun h0 _ h1 ->
     modifies1 res h0 h1 /\
     as_snat h1 res < as_snat h0 u /\
     as_snat h1 res = S.decrypt (as_spec_sk h0 #nLen p q n u sec_v g h)
                                (as_snat_bnlist #nLen #l h0 u_ps)
                                (as_snat_bnlist #nLen #l h0 u_es)
                                (as_snat h0 c)
     )
let decrypt #nLen #l p q n u u_ps u_es sec_v g h c res =
  bn_len_s_fits nLen;
  push_frame ();
  let hp0 = FStar.HyperStack.ST.get () in

  to_fe_idemp #(as_snat hp0 n) (as_snat hp0 c);
  let gv = create nLen (u64 0) in
  bn_modular_exp n g sec_v gv;
  let cv = create nLen (u64 0) in
  bn_modular_exp n c sec_v cv;

  admit ();

  pohlig_hellman n u_ps u_es gv cv res;

  pop_frame ()
