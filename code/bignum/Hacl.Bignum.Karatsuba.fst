module Hacl.Bignum.Karatsuba

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions
open Hacl.Bignum.Base
open Hacl.Impl.Lib

open Hacl.Bignum.Addition
open Hacl.Bignum.Multiplication

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module B = LowStar.Buffer
module Loops = Lib.LoopCombinators
module K = Hacl.Spec.Bignum.Karatsuba


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let bn_mul_threshold = size K.bn_mul_threshold

inline_for_extraction noextract
val bn_sign_abs:
    #t:limb_t
  -> #aLen:size_t
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> tmp:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (carry t)
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h tmp /\
    eq_or_disjoint a b /\ disjoint a res /\ disjoint b res /\
    disjoint a tmp /\ disjoint b tmp /\ disjoint tmp res)
  (ensures  fun h0 c h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    (c, as_seq h1 res) == K.bn_sign_abs (as_seq h0 a) (as_seq h0 b))

let bn_sign_abs #t #aLen a b tmp res =
  let c0 = bn_sub_eq_len aLen a b tmp in
  let c1 = bn_sub_eq_len aLen b a res in
  map2T aLen res (mask_select (uint #t 0 -. c0)) res tmp;
  c0


inline_for_extraction noextract
val bn_middle_karatsuba:
    #t:limb_t
  -> #aLen:size_t
  -> c0:carry t
  -> c1:carry t
  -> c2:carry t
  -> t01:lbignum t aLen
  -> t23:lbignum t aLen
  -> tmp:lbignum t aLen
  -> res:lbignum t aLen ->
  Stack (limb t)
  (requires fun h ->
    live h t01 /\ live h t23 /\ live h tmp /\ live h res /\
    disjoint t01 t23 /\ disjoint tmp res /\ disjoint t01 res /\
    disjoint t01 tmp /\ disjoint t23 tmp /\ disjoint t23 res)
  (ensures  fun h0 c h1 -> modifies (loc tmp |+| loc res) h0 h1 /\
    (c, as_seq h1 res) == K.bn_middle_karatsuba c0 c1 c2 (as_seq h0 t01) (as_seq h0 t23))

let bn_middle_karatsuba #t #aLen c0 c1 c2 t01 t23 tmp res =
  let c_sign = c0 ^. c1 in
  let c3 = bn_sub_eq_len aLen t01 t23 tmp in let c3 = c2 -. c3 in
  let c4 = bn_add_eq_len aLen t01 t23 res in let c4 = c2 +. c4 in
  let mask = uint #t 0 -. c_sign in
  map2T aLen res (mask_select mask) res tmp;
  mask_select mask c4 c3


inline_for_extraction noextract
val bn_lshift_add_in_place:
    #t:limb_t
  -> #aLen:size_t
  -> #bLen:size_t
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:size_t{v i + v bLen <= v aLen} ->
  Stack (carry t)
  (requires fun h -> live h a /\ live h b /\ disjoint a b)
  (ensures  fun h0 c h1 -> modifies (loc a) h0 h1 /\
    (c, as_seq h1 a) == K.bn_lshift_add (as_seq h0 a) (as_seq h0 b) (v i))

let bn_lshift_add_in_place #t #aLen #bLen a b i =
  let r = sub a i (aLen -! i) in
  let h0 = ST.get () in
  update_sub_f_carry h0 a i (aLen -! i)
  (fun h -> Hacl.Spec.Bignum.Addition.bn_add (as_seq h0 r) (as_seq h0 b))
  (fun _ -> bn_add (aLen -! i) r bLen b r)


inline_for_extraction noextract
val bn_lshift_add_early_stop_in_place:
    #t:limb_t
  -> #aLen:size_t
  -> #bLen:size_t
  -> a:lbignum t aLen
  -> b:lbignum t bLen
  -> i:size_t{v i + v bLen <= v aLen} ->
  Stack (carry t)
  (requires fun h -> live h a /\ live h b /\ disjoint a b)
  (ensures  fun h0 c h1 -> modifies (loc a) h0 h1 /\
    (c, as_seq h1 a) == K.bn_lshift_add_early_stop (as_seq h0 a) (as_seq h0 b) (v i))

let bn_lshift_add_early_stop_in_place #t #aLen #bLen a b i =
  let r = sub a i bLen in
  let h0 = ST.get () in
  update_sub_f_carry h0 a i bLen
  (fun h -> Hacl.Spec.Bignum.Addition.bn_add (as_seq h0 r) (as_seq h0 b))
  (fun _ -> bn_add_eq_len bLen r b r)


inline_for_extraction noextract
val bn_karatsuba_res:
    #t:limb_t
  -> #aLen:size_t{2 * v aLen <= max_size_t /\ 0 < v aLen}
  -> r01:lbignum t aLen
  -> r23:lbignum t aLen
  -> c5:limb t
  -> t45:lbignum t aLen
  -> res:lbignum t (aLen +! aLen) ->
  Stack (carry t)
  (requires fun h ->
    live h r01 /\ live h r23 /\ live h t45 /\ live h res /\ disjoint t45 res /\
    as_seq h res == LSeq.concat (as_seq h r01) (as_seq h r23))
  (ensures  fun h0 c h1 -> modifies (loc res) h0 h1 /\
    (c, as_seq h1 res) == K.bn_karatsuba_res (as_seq h0 r01) (as_seq h0 r23) c5 (as_seq h0 t45))

let bn_karatsuba_res #t #aLen r01 r23 c5 t45 res =
  push_frame ();
  let aLen2 = aLen /. 2ul in
  [@inline_let]
  let resLen = aLen +! aLen in
  let c6 = bn_lshift_add_early_stop_in_place res t45 aLen2 in
  let c7 = c5 +. c6 in
  let c7 = create 1ul c7 in
  let c8 = bn_lshift_add_in_place res c7 (aLen +! aLen2) in
  pop_frame ();
  c8


inline_for_extraction noextract
val bn_karatsuba_last:
    #t:limb_t
  -> aLen:size_t{4 * v aLen <= max_size_t /\ v aLen % 2 = 0 /\ 0 < v aLen}
  -> c0:carry t
  -> c1:carry t
  -> tmp:lbignum t (4ul *! aLen)
  -> res:lbignum t (aLen +! aLen) ->
  Stack (limb t)
  (requires fun h -> live h res /\ live h tmp /\ disjoint res tmp)
  (ensures  fun h0 c h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    (let sr01 = LSeq.sub (as_seq h0 res) 0 (v aLen) in
     let sr23 = LSeq.sub (as_seq h0 res) (v aLen) (v aLen) in
     let st23 = LSeq.sub (as_seq h0 tmp) (v aLen) (v aLen) in
     let sc2, st01 = Hacl.Spec.Bignum.Addition.bn_add sr01 sr23 in
     let sc5, sres = K.bn_middle_karatsuba c0 c1 sc2 st01 st23 in
     let sc, sres = K.bn_karatsuba_res sr01 sr23 sc5 sres in
     (c, as_seq h1 res) == (sc, sres)))

let bn_karatsuba_last #t aLen c0 c1 tmp res =
  let r01 = sub res 0ul aLen in
  let r23 = sub res aLen aLen in
  (**) let h = ST.get () in
  (**) LSeq.lemma_concat2 (v aLen) (as_seq h r01) (v aLen) (as_seq h r23) (as_seq h res);
  (**) assert (as_seq h res == LSeq.concat (as_seq h r01) (as_seq h r23));

  let t01 = sub tmp 0ul aLen in
  let t23 = sub tmp aLen aLen in
  let t45 = sub tmp (2ul *! aLen) aLen in
  let t67 = sub tmp (3ul *! aLen) aLen in

  let c2 = bn_add_eq_len aLen r01 r23 t01 in
  let c5 = bn_middle_karatsuba c0 c1 c2 t01 t23 t67 t45 in
  let c = bn_karatsuba_res r01 r23 c5 t45 res in
  c


#push-options "--z3rlimit 150"

val bn_karatsuba_mul_:
    #t:limb_t
  -> aLen:size_t{4 * v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> tmp:lbignum t (4ul *! aLen)
  -> res:lbignum t (aLen +! aLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\ live h tmp /\
    disjoint res tmp /\ disjoint tmp a /\ disjoint tmp b /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    as_seq h1 res == K.bn_karatsuba_mul_ (v aLen) (as_seq h0 a) (as_seq h0 b))

[@CInline]
let rec bn_karatsuba_mul_ #t aLen a b tmp res =
  let h0 = ST.get () in
  norm_spec [zeta; iota; primops; delta_only [`%K.bn_karatsuba_mul_]]
    (K.bn_karatsuba_mul_ (v aLen) (as_seq h0 a) (as_seq h0 b));
  if aLen <. bn_mul_threshold || aLen %. 2ul =. 1ul then
    bn_mul aLen a aLen b res
  else begin
    let aLen2 = aLen /. 2ul in

    let a0 = sub a 0ul aLen2 in
    let a1 = sub a aLen2 aLen2 in

    let b0 = sub b 0ul aLen2 in
    let b1 = sub b aLen2 aLen2 in

    // tmp = [ t0_aLen2; t1_aLen2; ..]
    let t0 = sub tmp 0ul aLen2 in
    let t1 = sub tmp aLen2 aLen2 in
    let tmp' = sub tmp aLen aLen2 in

    let c0 = bn_sign_abs a0 a1 tmp' t0 in
    let c1 = bn_sign_abs b0 b1 tmp' t1 in

    // tmp = [ t0_aLen2; t1_aLen2; t23_aLen; ..]
    (**) let h0 = ST.get () in
    let t23 = sub tmp aLen aLen in
    let tmp1 = sub tmp (aLen +! aLen) (aLen +! aLen) in
    bn_karatsuba_mul_ aLen2 t0 t1 tmp1 t23;

    let r01 = sub res 0ul aLen in
    let r23 = sub res aLen aLen in
    bn_karatsuba_mul_ aLen2 a0 b0 tmp1 r01;
    bn_karatsuba_mul_ aLen2 a1 b1 tmp1 r23;
    let c = bn_karatsuba_last aLen c0 c1 tmp res in
    () end

//TODO: pass tmp as a parameter?
inline_for_extraction noextract
val bn_karatsuba_mul:
    #t:limb_t
  -> aLen:size_t{0 < v aLen /\ 4 * v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> b:lbignum t aLen
  -> res:lbignum t (aLen +! aLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint res a /\ disjoint res b /\ eq_or_disjoint a b)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == K.bn_karatsuba_mul (as_seq h0 a) (as_seq h0 b))

let bn_karatsuba_mul #t aLen a b res =
  push_frame ();
  let tmp = create (4ul *! aLen) (uint #t 0) in
  bn_karatsuba_mul_ aLen a b tmp res;
  pop_frame ()


inline_for_extraction noextract
val bn_karatsuba_last_sqr:
    #t:limb_t
  -> aLen:size_t{4 * v aLen <= max_size_t /\ v aLen % 2 = 0 /\ 0 < v aLen}
  -> tmp:lbignum t (4ul *! aLen)
  -> res:lbignum t (aLen +! aLen) ->
  Stack (limb t)
  (requires fun h -> live h res /\ live h tmp /\ disjoint res tmp)
  (ensures  fun h0 c h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    (let sr01 = LSeq.sub (as_seq h0 res) 0 (v aLen) in
     let sr23 = LSeq.sub (as_seq h0 res) (v aLen) (v aLen) in
     let st23 = LSeq.sub (as_seq h0 tmp) (v aLen) (v aLen) in
     let sc2, st01 = Hacl.Spec.Bignum.Addition.bn_add sr01 sr23 in
     let sc5, sres = K.bn_middle_karatsuba_sqr sc2 st01 st23 in
     let sc, sres = K.bn_karatsuba_res sr01 sr23 sc5 sres in
     (c, as_seq h1 res) == (sc, sres)))

let bn_karatsuba_last_sqr #t aLen tmp res =
  let r01 = sub res 0ul aLen in
  let r23 = sub res aLen aLen in
  (**) let h = ST.get () in
  (**) LSeq.lemma_concat2 (v aLen) (as_seq h r01) (v aLen) (as_seq h r23) (as_seq h res);
  (**) assert (as_seq h res == LSeq.concat (as_seq h r01) (as_seq h r23));

  let t01 = sub tmp 0ul aLen in
  let t23 = sub tmp aLen aLen in
  let t45 = sub tmp (2ul *! aLen) aLen in

  let c2 = bn_add_eq_len aLen r01 r23 t01 in
  let c3 = bn_sub_eq_len aLen t01 t23 t45 in
  let c5 = c2 -. c3 in
  let c = bn_karatsuba_res r01 r23 c5 t45 res in
  c


val bn_karatsuba_sqr_:
    #t:limb_t
  -> aLen:size_t{4 * v aLen <= max_size_t /\ 0 < v aLen}
  -> a:lbignum t aLen
  -> tmp:lbignum t (4ul *! aLen)
  -> res:lbignum t (aLen +! aLen) ->
  Stack unit
  (requires fun h ->
    live h a /\ live h res /\ live h tmp /\
    disjoint res tmp /\ disjoint tmp a /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res |+| loc tmp) h0 h1 /\
    as_seq h1 res == K.bn_karatsuba_sqr_ (v aLen) (as_seq h0 a))

[@CInline]
let rec bn_karatsuba_sqr_ #t aLen a tmp res =
  let h0 = ST.get () in
  norm_spec [zeta; iota; primops; delta_only [`%K.bn_karatsuba_sqr_]]
    (K.bn_karatsuba_sqr_ (v aLen) (as_seq h0 a));
  if aLen <. bn_mul_threshold || aLen %. 2ul =. 1ul then
    bn_sqr aLen a res
  else begin
    let aLen2 = aLen /. 2ul in

    let a0 = sub a 0ul aLen2 in
    let a1 = sub a aLen2 aLen2 in

    let t0 = sub tmp 0ul aLen2 in
    let tmp' = sub tmp aLen aLen2 in
    let c0 = bn_sign_abs a0 a1 tmp' t0 in

    let t23 = sub tmp aLen aLen in
    let tmp1 = sub tmp (aLen +! aLen) (aLen +! aLen) in
    bn_karatsuba_sqr_ aLen2 t0 tmp1 t23;

    let r01 = sub res 0ul aLen in
    let r23 = sub res aLen aLen in
    bn_karatsuba_sqr_ aLen2 a0 tmp1 r01;
    bn_karatsuba_sqr_ aLen2 a1 tmp1 r23;
    let c = bn_karatsuba_last_sqr aLen tmp res in
    () end


//TODO: pass tmp as a parameter?
inline_for_extraction noextract
val bn_karatsuba_sqr:
    #t:limb_t
  -> aLen:size_t{0 < v aLen /\ 4 * v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> res:lbignum t (aLen +! aLen) ->
  Stack unit
  (requires fun h -> live h a /\ live h res /\ disjoint res a)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == K.bn_karatsuba_sqr (as_seq h0 a))

let bn_karatsuba_sqr #t aLen a res =
  push_frame ();
  let tmp = create (4ul *! aLen) (uint #t 0) in
  bn_karatsuba_sqr_ aLen a tmp res;
  pop_frame ()
