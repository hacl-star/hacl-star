module Hacl.Spec.Bignum.Base

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let carry (t:limb_t) = x:limb t{uint_v x == 0 \/ uint_v x == 1}

(**
 This is non-stateful version of code/fallback functions
*)
inline_for_extraction noextract
val addcarry: #t:limb_t -> c:carry t -> a:limb t -> b:limb t ->
  Pure (carry t & limb t)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r + uint_v c' * pow2 (bits t) == uint_v a + uint_v b + uint_v c)

let addcarry #t cin x y =
  let res = x +. cin +. y in
  let c = logand (logor (lt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) in
  logand_lemma (eq_mask res x) cin;
  logor_lemma (lt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (lt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) 1;
  c, res


inline_for_extraction noextract
val subborrow: #t:limb_t -> c:carry t -> a:limb t -> b:limb t ->
  Pure (carry t & limb t)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r - uint_v c' * pow2 (bits t) == uint_v a - uint_v b - uint_v c)

let subborrow #t cin x y =
  let res = x -. y -. cin in
  let c = logand (logor (gt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) in
  logand_lemma (eq_mask res x) cin;
  logor_lemma (gt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (gt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) 1;
  c, res


inline_for_extraction noextract
val mul_wide: #t:limb_t -> a:limb t -> b:limb t ->
  Pure (tuple2 (limb t) (limb t))
  (requires True)
  (ensures  fun (hi, lo) ->
    v lo + v hi * pow2 (bits t) == v a * v b)

let mul_wide #t a b =
  Math.Lemmas.lemma_mult_lt_sqr (v a) (v b) (pow2 (bits t));
  match t with
  | U32 ->
    let res = to_u64 a *! to_u64 b in
    to_u32 (res >>. 32ul), to_u32 res
  | U64 ->
    let res = mul64_wide a b in
    to_u64 (res >>. 64ul), to_u64 res


inline_for_extraction noextract
let mask_values (#t:limb_t) (x:limb t) =
  v x = v (zeros t SEC) \/ v x = v (ones t SEC)


inline_for_extraction noextract
let unsafe_bool_of_limb0 (#t:limb_t) (m:limb t) : b:bool{b <==> v m = 0} =
  let open Lib.RawIntTypes in
  match t with
  | U32 -> FStar.UInt32.(u32_to_UInt32 m =^ 0ul)
  | U64 -> FStar.UInt64.(u64_to_UInt64 m =^ 0uL)


inline_for_extraction noextract
let unsafe_bool_of_limb (#t:limb_t) (m:limb t) : b:bool{b <==> v m = v (ones t SEC)} =
  let open Lib.RawIntTypes in
  match t with
  | U32 -> FStar.UInt32.(u32_to_UInt32 m =^ u32_to_UInt32 (ones U32 SEC))
  | U64 -> FStar.UInt64.(u64_to_UInt64 m =^ u64_to_UInt64 (ones U64 SEC))


inline_for_extraction noextract
let size_to_limb (#t:limb_t) (x:size_t) : limb t =
  match t with
  | U32 -> size_to_uint32 x
  | U64 -> size_to_uint64 x


inline_for_extraction noextract
val mask_select: #t:limb_t -> mask:limb t -> a:limb t -> b:limb t -> limb t
let mask_select #t mask a b =
  (mask &. a) |. ((lognot mask) &. b)

val mask_select_lemma: #t:limb_t -> mask:limb t -> a:limb t -> b:limb t -> Lemma
  (requires mask_values mask)
  (ensures  mask_select mask a b == (if v mask = 0 then b else a))

let mask_select_lemma #t mask a b =
  if v mask = 0 then begin
    logand_lemma mask a;
    assert (v (mask &. a) = 0);
    lognot_lemma mask;
    assert (v (lognot mask) = v (ones t SEC));
    logand_lemma (lognot mask) b;
    assert (v ((lognot mask) &. b) == v b);
    logor_lemma (mask &. a) ((lognot mask) &. b);
    assert (v (mask_select mask a b) == v b) end
  else begin
    logand_lemma mask a;
    assert (v (mask &. a) = v a);
    lognot_lemma mask;
    assert (v (lognot mask) = 0);
    logand_lemma (lognot mask) b;
    assert (v ((lognot mask) &. b) == 0);
    logor_zeros (mask &. a);
    assert (v (mask_select mask a b) == v a) end


val mask_select_lemma1: #t:limb_t -> mask:limb t -> a:limb t -> b:limb t -> Lemma
  (requires mask_values mask)
  (ensures  b ^. (mask &. (a ^. b)) == (if v mask = 0 then b else a))

let mask_select_lemma1 #t mask a b =
  let t1 = mask &. (a ^. b) in
  let t2 = b ^. t1 in
  logand_lemma mask (a ^.b);
  if v mask = 0 then begin
    assert (v t1 == 0);
    logxor_lemma b t1;
    assert (v t2 = v b);
    () end
  else begin
    assert (v t1 == v (a ^. b));
    logxor_lemma b a;
    assert (v t2 = v a);
    () end


val lseq_mask_select_lemma: #t:limb_t -> #len:size_nat -> a:lseq (limb t) len -> b:lseq (limb t) len -> mask:limb t -> Lemma
  (requires mask_values mask)
  (ensures  map2 (mask_select mask) a b == (if v mask = 0 then b else a))

let lseq_mask_select_lemma #t #len a b mask =
  let res = map2 (mask_select mask) a b in

  let lemma_aux (i:nat{i < len}) : Lemma (v res.[i] == (if v mask = 0 then v b.[i] else v a.[i])) =
    mask_select_lemma mask a.[i] b.[i] in

  Classical.forall_intro lemma_aux;
  if v mask = 0 then eq_intro res b else eq_intro res a
