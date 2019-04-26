module Hacl.Symmetric.GCM.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Seq
open FStar.BitVector
open FStar.Math.Lemmas

(*
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8

let u8  = U8.t
let u32 = U32.t
let s8  = H8.t
*)

type bv128 = bv_t 128

abstract val seqbv_bv: #n:pos ->
    a:seq (bv_t 8){length a = n} ->
    Tot (r:bv_t (n * 8){forall (i:nat{i < n * 8}). index r i = index (index a (i / 8)) (i % 8)})
let rec seqbv_bv #n a =
  if n = 1 then index a 0 else
  append (index a 0) (seqbv_bv #(n - 1) (slice a 1 n))

abstract val gf128_add_pure_loop: #n:pos ->
    a:seq (bv_t 8){length a = n} ->
    b:seq (bv_t 8){length b = n} ->
    Tot (r:seq (bv_t 8){length r = n /\ (forall (i:nat{i < n}). equal (index r i) (logxor_vec (index a i) (index b i)))})
let rec gf128_add_pure_loop #n a b =
  if n = 1 then create 1 (logxor_vec (index a 0) (index b 0)) else
  append (create 1 (logxor_vec (index a 0) (index b 0))) (gf128_add_pure_loop #(n - 1) (slice a 1 n) (slice b 1 n))
  
val gf128_add: bv128 -> bv128 -> Tot bv128
let gf128_add a b = logxor_vec #128 a b

val gf128_add_lemma: a:seq (bv_t 8){length a = 16} ->
    b:seq (bv_t 8){length b = 16} ->
    Lemma (equal (seqbv_bv #16 (gf128_add_pure_loop #16 a b)) (gf128_add (seqbv_bv #16 a) (seqbv_bv #16 b)))
let gf128_add_lemma a b = ()

abstract val gf128_shift_right_pure_loop: #n:pos ->
    a:seq (bv_t 8){length a = n} ->
    Tot (r:seq (bv_t 8){length r = n /\ equal (index r 0) (shift_right_vec (index a 0) 1) /\ (forall (i:pos{i < n}). index (index r i) 0 = index (index a (i - 1)) 7) /\ (forall (i:pos{i < n}). forall (j:pos{j < 8}). index (index r i) j = index (index a i) (j - 1))})
let rec gf128_shift_right_pure_loop #n a =
  if n = 1 then create 1 (shift_right_vec (index a 0) 1) else
  append (gf128_shift_right_pure_loop #(n - 1) (slice a 0 (n - 1))) (create 1 (append (slice (index a (n - 2)) 7 8) (slice (index a (n - 1)) 0 7)))

val gf128_shift_right: bv128 -> Tot bv128
let gf128_shift_right a = shift_right_vec #128 a 1

val gf128_shift_right_lemma_aux_1: a:seq (bv_t 8){length a = 16} ->
    Lemma (forall (i:pos{i < 128 /\ i % 8 = 0}). index (gf128_shift_right (seqbv_bv #16 a)) i = index (seqbv_bv #16 (gf128_shift_right_pure_loop #16 a)) i)
let gf128_shift_right_lemma_aux_1 a =
  assert(forall (i:pos). i % 8 = 0 ==> (i - 1) / 8 = i / 8 - 1 /\ (i - 1) % 8 = 7);
  assert(forall (i:pos{i < 128 /\ i % 8 = 0}). index (gf128_shift_right (seqbv_bv #16 a)) i = index (index a (i / 8 - 1)) 7);
  assert(forall (i:pos{i < 128 /\ i % 8 = 0}). index (seqbv_bv #16 (gf128_shift_right_pure_loop #16 a)) i = index (index a (i / 8 - 1)) 7)

val gf128_shift_right_lemma_aux_2: a:seq (bv_t 8){length a = 16} ->
    Lemma (forall (i:pos{i < 128 /\ i % 8 > 0}). index (gf128_shift_right (seqbv_bv #16 a)) i = index (seqbv_bv #16 (gf128_shift_right_pure_loop #16 a)) i)
let gf128_shift_right_lemma_aux_2 a =
  assert(forall (i:pos). i % 8 > 0 ==> (i - 1) / 8 = i / 8 /\ (i - 1) % 8 = i % 8 - 1);
  assert(forall (i:pos{i < 128 /\ i % 8 > 0}). index (gf128_shift_right (seqbv_bv #16 a)) i = index (index a (i / 8)) (i % 8 - 1));
  assert(forall (i:pos{i < 128 /\ i % 8 > 0}). index (seqbv_bv #16 (gf128_shift_right_pure_loop #16 a)) i = index (index a (i / 8)) (i % 8 - 1))

val gf128_shift_right_lemma: a:seq (bv_t 8){length a = 16} ->
    Lemma (equal (seqbv_bv #16 (gf128_shift_right_pure_loop #16 a)) (gf128_shift_right (seqbv_bv #16 a)))
let gf128_shift_right_lemma a =
  gf128_shift_right_lemma_aux_1 a; gf128_shift_right_lemma_aux_2 a
(*
val apply_mask: a:bv128 -> msk:bv128{equal msk (ones_vec #128) \/ equal msk (zero_vec #128)} -> Tot (r:bv128{(equal msk (ones_vec #128) ==> equal r a) /\ (equal msk (zero_vec #128) ==> equal r (zero_vec #128))})
let apply_mask a msk = logand_vec a msk
*)

val gf128_shift_left: bv128 -> Tot bv128
let gf128_shift_left a = shift_left_vec #128 a 1

assume val r_mul: bv128

val gf128_shift_right_mod: bv128 -> Tot bv128
let gf128_shift_right_mod a =
  if index a 127 then gf128_add r_mul (gf128_shift_right a)
  else gf128_shift_right a

val gf128_mul_pure_loop: a:bv128 -> b:bv128 -> r:bv128 -> dep:nat{dep <= 128} -> Tot bv128 (decreases (128 - dep))
let rec gf128_mul_pure_loop a b r dep =
  if dep = 128 then r
  else if index b dep then gf128_mul_pure_loop (gf128_shift_right_mod a) b (gf128_add r a) (dep + 1)
  else gf128_mul_pure_loop (gf128_shift_right_mod a) b r (dep + 1)

val gf128_mul: bv128 -> bv128 -> Tot bv128
let gf128_mul a b = gf128_mul_pure_loop a b (zero_vec #128) 0

assume val mk_len_info: len_1:nat -> len_2:nat -> Tot bv128

assume val ghash_loop_: otag:bv128 ->
    auth_key:bv128 ->
    #len:nat ->
    str:bv_t len ->
    dep:nat{dep <= len} ->
    Tot (ntag: bv128 {(len - dep = 0 /\ ntag = gf128_mul auth_key (gf128_add otag (zero_vec #128))) \/ (len - dep < 128 /\ ntag = gf128_mul auth_key (gf128_add otag (append (slice str dep len) (zero_vec #(128 - len + dep))))) \/ (len - dep = 128 /\ ntag = gf128_mul auth_key (gf128_add otag (slice str dep (dep + 128))))})
(* Actually for this function we only need to prove that the original code:  *)
(*     let last = create (uint8_to_sint8 0uy) 16ul in                        *)
(*     blit str dep last 0ul (U32 (len -^ dep))                              *)
(* will expand a short bitvector to gf128 by adding certain number of zeros. *)

val ghash_loop: otag:bv128 ->
    auth_key:bv128 ->
    #len:nat ->
    str:bv_t len ->
    dep:nat{dep <= len} ->
    Tot (ntag:bv128) (decreases (len - dep))
let rec ghash_loop otag auth_key #len str dep =
  if len - dep <= 128 then begin
    ghash_loop_ otag auth_key #len str dep
  end else begin
    let si = slice str dep (dep + 128) in
    let tag_1 = gf128_add otag si in
    let tag_2 = gf128_mul auth_key tag_1 in
    let tag_3 = ghash_loop tag_2 auth_key #len str (dep + 128) in
    tag_3
  end

val ghash_loop_lemma_1: otag:bv128 ->
    auth_key:bv128 ->
    #len:nat ->
    str:bv_t len ->
    dep:nat{dep <= len /\ len - dep <= 128} ->
    Lemma (ghash_loop otag auth_key #len str dep = ghash_loop_ otag auth_key #len str dep)
let ghash_loop_lemma_1 otag auth_key #len str dep = ()

val ghash_loop_lemma_2:otag:bv128 ->
    auth_key:bv128 ->
    #len:nat ->
    str:bv_t len ->
    dep:nat{len - dep > 128} ->
    Lemma (ghash_loop otag auth_key #len str dep = ghash_loop (gf128_mul auth_key (gf128_add otag (slice str dep (dep + 128)))) auth_key #len str (dep + 128))
let ghash_loop_lemma_2 otag auth_key #len str dep = ()

val ghash: auth_key:bv128 ->
    #adlen:nat ->
    ad:bv_t adlen ->
    #len:nat ->
    ciphertext:bv_t len ->
    Tot (tag:bv128{tag = gf128_mul auth_key (gf128_add (mk_len_info adlen len) (ghash_loop (ghash_loop (zero_vec #128) auth_key #adlen ad 0) auth_key #len ciphertext 0))})
let ghash auth_key #adlen ad #len ciphertext =
  let len_info = mk_len_info adlen len in
  let tag_0 = zero_vec #128 in
  let tag_1 = ghash_loop tag_0 auth_key #adlen ad 0 in
  let tag_2 = ghash_loop tag_1 auth_key #len ciphertext 0 in
  let tag_3 = gf128_add len_info tag_2 in
  let tag_4 = gf128_mul auth_key tag_3 in
  tag_4
