module Hacl.Symmetric.GCM.Lemmas

open FStar.Mul
open FStar.Seq
open FStar.BitVector

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8

let u8  = U8.t
let u32 = U32.t
let s8  = H8.t

type bv128 = bv_t 128

val seqbv_bv: #n:pos ->
    a:seq (bv_t 8){length a = n} ->
    Tot (r:bv_t (n * 8){forall (i:nat{i < n * 8}). index r i = index (index a (i / 8)) (i % 8)})
let rec seqbv_bv #n a =
  if n = 1 then index a 0 else
  append (index a 0) (seqbv_bv #(n - 1) (slice a 1 n))

val bv_seqbv: #n:pos ->
    a:bv_t (n * 8) ->
    Tot (r:seq (bv_t 8){length r = n /\ (forall (i:nat{i < n * 8}). index a i = index (index r (i / 8)) (i % 8))})
let rec bv_seqbv #n a =
  if n = 1 then create #(bv_t 8) 1 (slice a 0 8) else begin
  let r = append (create #(bv_t 8) 1 (slice a 0 8)) (bv_seqbv #(n - 1) (slice a 8 (n * 8))) in
  admit();
  r
  end

val gf128_add_pure_loop: a:seq (bv_t 8) ->
    b:seq (bv_t 8) ->
    dep:nat{dep <= 16} ->
    Tot seq (bv_t 8)
let gf128_add_pure_loop a b dep = admit()
  

val gf128_add: bv128 -> bv128 -> Tot bv128
let gf128_add a b = logand_vec #128 a b

val gf128_shift_right: bv128 -> Tot bv128
let gf128_shift_right a = shift_right_vec #128 a 1

val apply_mask: bv128 -> bv128 -> Tot bv128
let apply_mask a msk = logand_vec a msk

val gf128_mul: bv128 -> bv128 -> Tot bv128
let gf128_mul a b = admit()

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
    let tag_2 = gf128_mul tag_1 auth_key in
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
  let tag_3 = gf128_add tag_2 len_info in
  let tag_4 = gf128_mul tag_3 auth_key in
  tag_4
