module Hacl.IntTypes.Intrinsics

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

#set-options "--fuel 0 --ifuel 0 --z3rlimit 500"

inline_for_extraction noextract
val cast_to : t:inttype{t = U32 \/ t = U64} ->
  t':inttype{if t = U32 then t' = U64 else t' = U128} ->
  (u1:int_t t SEC{unsigned t' \/ range (v u1) t'}
  -> u2:int_t t' SEC{v u2 == v u1 @%. t'})
let cast_to t t' =
  match t with
  | U32 -> cast U64 SEC
  | U64 -> cast U128 SEC

inline_for_extraction noextract
val cast_from : t:inttype{t = U64 \/ t = U128} ->
  t':inttype{if t = U64 then t' = U32 else t' = U64} ->
  (u1:int_t t SEC{unsigned t' \/ range (v u1) t'}
  -> u2:int_t t' SEC{v u2 == v u1 @%. t'})
let cast_from t t' =
  match t with
  | U64 -> cast U32 SEC
  | U128 -> cast U64 SEC

inline_for_extraction noextract
let add_carry_st (t:inttype{t = U32 \/ t = U64}) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:lbuffer (uint_t t SEC) (size 1) ->
  Stack (uint_t t SEC)
  (requires fun h -> live h r /\ v cin <= 1)
  (ensures  fun h0 c h1 ->
    modifies1 r h0 h1 /\ v c <= 1 /\
    (let r = Seq.index (as_seq h1 r) 0 in
    v r + v c * pow2 (bits t) == v x + v y + v cin))

inline_for_extraction noextract
val add_carry:
  t:inttype{t = U32 \/ t = U64} ->
  t':inttype{if t = U32 then t' = U64 else t' = U128} ->
  shift_bits:UInt32.t{if t = U32 then shift_bits == 32ul else shift_bits == 64ul} ->
  add_carry_st t
let add_carry t t' shift_bits cin x y r =
  let res = cast_to t t' x +. cast_to t t' cin +. cast_to t t'  y in
  let c = cast_from t' t (res >>. shift_bits) in
  r.(0ul) <- cast_from t' t res;
  c

val add_carry_u32: add_carry_st U32
let add_carry_u32 = add_carry U32 U64 32ul


inline_for_extraction noextract
val to_uint : t:inttype{t = U32 \/ t = U64} ->
  (n:range_t t -> u:int_t t SEC{v u == n})
let to_uint t =
  match t with
  | U32 -> u32
  | U64 -> u64

inline_for_extraction noextract
let sub_borrow_st (t:inttype{t = U32 \/ t = U64}) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:lbuffer (uint_t t SEC) (size 1) ->
  Stack (uint_t t SEC)
  (requires fun h -> live h r /\ v cin <= 1)
  (ensures  fun h0 c h1 ->
    modifies1 r h0 h1 /\ v c <= 1 /\
    (let r = Seq.index (as_seq h1 r) 0 in
    v r - v c * pow2 (bits t) == v x - v y - v cin))

#push-options "--z3rlimit 1000 --max_fuel 1"

inline_for_extraction noextract
val sub_borrow:
  t:inttype{t = U32 \/ t = U64} ->
  t':inttype{if t = U32 then t' = U64 else t' = U128} ->
  shift_bits:UInt32.t{if t = U32 then shift_bits == 32ul else shift_bits == 64ul} ->
  p:UInt32.t{if t = U32 then p == 64ul else p == 128ul} ->
  sub_borrow_st t
let sub_borrow t t' shift_bits p cin x y r =
  let res = cast_to t t' x -. cast_to t t' y -. cast_to t t' cin in
  assert (v res == ((v x - v y) % pow2 (v p) - v cin) % pow2 (v p));
  Math.Lemmas.lemma_mod_add_distr (- v cin) (v x - v y) (pow2 (v p));
  assert (v res == (v x - v y - v cin) % pow2 (v p));

  assert (v res % pow2 (v shift_bits) = (v x - v y - v cin) % pow2 (v p) % pow2 (v shift_bits));
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (v x - v y - v cin) (v shift_bits) (v p);
  assert (v res % pow2 (v shift_bits) = (v x - v y - v cin) % pow2 (v shift_bits));

  let c = cast_from t' t (res >>. shift_bits) &. (to_uint t 1) in
  assert_norm (pow2 1 = 2);
  mod_mask_lemma (cast_from t' t (res >>. shift_bits)) 1ul;
  assert (v ((mk_int #t #SEC 1 <<. 1ul) -! mk_int 1) == 1);
  assert (v c = v res / pow2 (v shift_bits) % pow2 1);

  r.(0ul) <- cast_from t' t res;
  assert (v c = (if 0 <= v x - v y - v cin then 0 else 1));
  c

val sub_borrow_u32: sub_borrow_st U32
let sub_borrow_u32 = sub_borrow U32 U64 32ul 64ul


(* Fallback versions of add_carry_u64 and sub_borrow_u64 for platforms which
   don't support uint128.
   The names Hacl.IntTypes.Intrinsics.add_carry_u64 and sub_borrow_u64 must not
   be changed because they are hardcoded in KreMLin for extracting wasm code
   which uses these intrinsics. *)
inline_for_extraction noextract
val add_carry_fallback: #t:inttype{t = U32 \/ t = U64} -> add_carry_st t
let add_carry_fallback #t cin x y r =
  let res = x +. cin +. y in
  let c = logand (logor (lt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) in
  r.(0ul) <- res;
  logand_lemma (eq_mask res x) cin;
  logor_lemma (lt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (lt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) 1;
  c

val add_carry_u64: add_carry_st U64
let add_carry_u64 cin x y r = add_carry_fallback #U64 cin x y r

inline_for_extraction noextract
val sub_borrow_fallback: #t:inttype{t = U32 \/ t = U64} -> sub_borrow_st t
let sub_borrow_fallback #t cin x y r =
  let res = x -. y -. cin in
  let c = logand (logor (gt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) in
  logand_lemma (eq_mask res x) cin;
  logor_lemma (gt_mask res x) (logand (eq_mask res x) cin);
  logand_mask (logor (gt_mask res x) (logand (eq_mask res x) cin)) (uint #t 1) 1;
  r.(0ul) <- res;
  c

val sub_borrow_u64: sub_borrow_st U64
let sub_borrow_u64 cin x y r = sub_borrow_fallback #U64 cin x y r
