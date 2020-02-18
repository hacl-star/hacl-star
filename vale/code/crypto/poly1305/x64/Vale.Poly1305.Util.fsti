module Vale.Poly1305.Util

open FStar.Mul
open Vale.Def.Prop_s
open Vale.Def.Opaque_s
open Vale.Poly1305.Spec_s
open Vale.X64.Machine_s
open Vale.Poly1305.Math
open Vale.X64.State
open Vale.X64.Decls
open Vale.Def.Opaque_s
open Vale.X64.Memory

let rec poly1305_heap_blocks'
    (h:int) (pad:int) (r:int) (s:Seq.seq nat64) (k:int{0 <= k /\ k <= Seq.length s /\ k % 2 == 0})
  : Tot int (decreases k) =
  if k = 0 then h
  else
    let kk = k - 2 in
    let hh = poly1305_heap_blocks' h pad r s kk in
    modp ((hh + pad + pow2_64 * Seq.index s (kk + 1) + Seq.index s kk) * r)

val poly1305_heap_blocks (h:int) (pad:int) (r:int) (s:Seq.seq nat64) (k:int) : int

val reveal_poly1305_heap_blocks (h:int) (pad:int) (r:int) (s:Seq.seq nat64) (k:int) : Lemma
  (requires 0 <= k /\ k <= Seq.length s /\ k % 2 == 0)
  (ensures poly1305_heap_blocks h pad r s k = poly1305_heap_blocks' h pad r s k)

type t_seqTo128 = int -> nat128
let seqTo128 (s:Seq.seq nat64) : t_seqTo128 =
  let f (i:int) : nat128 =
    if 0 <= i && i < Seq.length s / 2 then
      (Seq.index s (2 * i)) + 0x10000000000000000 * (Seq.index s (2 * i + 1))
    else
      42
  in f
let seqTo128_app (s:Seq.seq nat64) (i:int) : nat128 = seqTo128 s i

val lemma_poly1305_heap_hash_blocks_alt (h:int) (pad:int) (r:int) (m:vale_heap) (b:buffer64) (n:int) : Lemma
  (requires 0 <= n /\ n + n <= buffer_length b /\ n + n <= Seq.length (buffer64_as_seq m b))
  (ensures
    ((n + n) % 2) == 0 /\ // REVIEW
    poly1305_heap_blocks h pad r (buffer64_as_seq m b) (n + n) ==
    poly1305_hash_blocks h pad r (seqTo128 (buffer64_as_seq m b)) n)

let rec buffers_readable (h:vale_heap) (l:list buffer64) : GTot Type0 (decreases l) =
  match l with
  | [] -> True
  | b :: l'  -> buffer_readable h b /\ buffers_readable h l'

unfold let modifies_buffer (b:buffer64) (h1 h2:vale_heap) = modifies_mem (loc_buffer b) h1 h2

let readable_words (len:nat) =
  ((len + 15) / 16) * 2 // 2 == 16 for rounding /8 for 8-byte words

val lemma_equal_blocks (h pad r:int) (inp1 inp2:int -> nat128) (k:nat) : Lemma
  (requires
    (forall (i:int).{:pattern (inp1 i)} 0 <= i /\ i < k ==> inp1 i == inp2 i)
  )
  (ensures (
    let hh1 = poly1305_hash_blocks h pad r inp1 k in
    let hh2 = poly1305_hash_blocks h pad r inp2 k in
    hh1 == hh2
  ))

val lemma_append_blocks (h pad r:int) (inp1 inp2 inp:int -> nat128) (k1 k2:nat) : Lemma
  (requires
    (forall (i:int).{:pattern (inp1 i)} 0 <= i /\ i < k1 ==> inp1 i == inp i) /\
    (forall (i:int).{:pattern (inp2 i)} 0 <= i /\ i < k2 ==> inp2 i == inp (i + k1))
  )
  (ensures (
    let hh1 = poly1305_hash_blocks h pad r inp1 k1 in
    let hh2 = poly1305_hash_blocks hh1 pad r inp2 k2 in
    hh2 == poly1305_hash_blocks h pad r inp (k1 + k2)
  ))

