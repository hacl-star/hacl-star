(* A large chunk of this module is taken from FStar/examples/low-level/crypto *)
module Hacl.Spec.Poly1305_64.Lemmas1

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Endianness

open Spec.Poly1305
open Spec.Chacha20Poly1305


module U8 = FStar.UInt8


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private val append_empty: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma
  (requires (Seq.length s1 == 0))
  (ensures  (Seq.append s1 s2 == s2))
  [SMTPat (Seq.append s1 s2); SMTPat (Seq.length s1 == 0)]
let append_empty #a s1 s2 =
  Seq.lemma_eq_intro (Seq.append s1 s2) s2

private val append_cons_snoc: #a:Type -> s1:Seq.seq a -> hd:a -> tl:Seq.seq a -> Lemma
  (Seq.append s1 (Seq.cons hd tl) ==
   Seq.append (Seq.snoc s1 hd) tl)
let append_cons_snoc #a s1 hd tl =
  Seq.lemma_eq_intro
    (Seq.append s1 (Seq.cons hd tl))
    (Seq.append (Seq.snoc s1 hd) tl)

private val snoc_cons: #a:Type -> s:Seq.seq a -> x:a -> y:a -> Lemma
  (FStar.Seq.(Seq.equal (snoc (cons x s) y) (cons x (snoc s y))))
let snoc_cons #a s x y = ()

private val append_assoc: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> s3:Seq.seq a -> Lemma
  (FStar.Seq.(equal (append s1 (append s2 s3)) (append (append s1 s2) s3)))
let append_assoc #a s1 s2 s3 = ()


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

private val encode_bytes_empty: txt:Seq.seq U8.t -> Lemma
    (requires Seq.length txt == 0)
    (ensures  encode_bytes (txt) == Seq.createEmpty)
    [SMTPat (encode_bytes (txt)); SMTPat (Seq.length txt == 0)]
let encode_bytes_empty txt = ()


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

private val snoc_encode_bytes: s:Seq.seq U8.t -> w:word_16 -> Lemma
  (Seq.equal (Seq.snoc (encode_bytes ( s)) ( w)) (encode_bytes ((Seq.append w s))))
let snoc_encode_bytes s w =
  let txt0, txt1 = Seq.split (Seq.append w s) 16 in
  assert (Seq.equal w txt0 /\ Seq.equal s txt1)


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

module U32 = FStar.UInt32

val encode_bytes_append: len:nat -> s:Seq.seq U8.t -> w:word -> Lemma
  (requires (0 < Seq.length w /\ Seq.length s == len /\ len % 16 == 0))
  (ensures  (Seq.equal (encode_bytes ((Seq.append s w)))
                      (Seq.cons (w) (encode_bytes (s)))))
  (decreases (Seq.length s))
let rec encode_bytes_append len s w =
  let open FStar.Seq in
  let open FStar.Seq in
  let txt = Seq.append s w in
  lemma_len_append s w;
  let l0 = Math.Lib.min (length txt) 16 in
  let w', txt = split_eq txt l0 in
  if length s = 0 then
    begin
    assert (equal w w');
    encode_bytes_empty txt
    end
  else
    begin
    assert (l0 == 16);
    let w0, s' = split_eq s 16 in
    snoc_encode_bytes (append s' w) w0;
    append_assoc w0 s' w;
    snoc_cons (encode_bytes ( s')) ( w) ( w0);
    encode_bytes_append (len - 16) s' w
    end


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


val lemma_encode_bytes_append: s1:Seq.seq U8.t -> s2:Seq.seq U8.t -> l:nat{l * 16 = length s1} ->
  Lemma (requires (True))
        (ensures (encode_bytes (s1 @| s2) == encode_bytes s2 @| encode_bytes s1))
        (decreases (l))
let rec lemma_encode_bytes_append s1 s2 l =
  if l = 0 then (
    encode_bytes_empty s1;
    Seq.lemma_eq_intro (encode_bytes s2) (encode_bytes s2 @| encode_bytes s1);
    Seq.lemma_eq_intro (s2) (s1 @| s2))
  else (
    cut (length s1 >= 16);
    let s1', s1'' = split s1 (length s1 - 16) in
    append_assoc s1' s1'' s2;
    Seq.lemma_eq_intro (s1' @| (s1'' @| s2)) (s1 @| s2);
    lemma_encode_bytes_append s1' (s1'' @| s2) (l-1);
    cut (encode_bytes (s1 @| s2) == encode_bytes (s1'' @| s2) @| encode_bytes s1');
    snoc_encode_bytes s2 s1'';
    Seq.lemma_eq_intro (encode_bytes (s1'' @| s2)) (snoc (encode_bytes s2) s1'');
    cut (encode_bytes (s1 @| s2) == (snoc (encode_bytes s2) s1'') @| encode_bytes s1');
    append_assoc (encode_bytes s2) (Seq.create 1 s1'') (encode_bytes s1');
    cut (encode_bytes (s1 @| s2) == encode_bytes s2 @| (cons s1'' (encode_bytes s1')));
    encode_bytes_append (length s1') s1' s1'';
    Seq.lemma_eq_intro (encode_bytes (s1' @| s1'')) (cons s1'' (encode_bytes s1'));
    Seq.lemma_eq_intro (s1' @| s1'') s1
  )

private val lemma_append_empty: #a:Type -> s:seq a -> Lemma
  (s @| createEmpty #a == s)
let lemma_append_empty #a s = Seq.lemma_eq_intro s (s @| createEmpty #a)
     

#reset-options "--max_fuel 0 --z3rlimit 100"

private let lemma_tl (log:text) (m:word_16) (log':text) : Lemma
  (requires (log' == create 1 ( m) @| log))
  (ensures (length log' > 0 /\ (Seq.tail log' == log) /\ (Seq.head log' == ( m))))
  = Seq.lemma_eq_intro (tail log') log;
    cut (Seq.index log' 0 == (m))


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let poly_def_0 (log:text{length log = 0}) (r:elem) : Lemma
  (poly log r = zero)
   = ()

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

let poly_def_1 (log:text{length log > 0}) (r:elem) : Lemma
  (let hd = Seq.head log in
   let tl = Seq.tail log in
   poly log r = (poly tl r +@ encode hd) *@ r)
   = ()


#reset-options "--max_fuel 0 --z3rlimit 1000"

val lemma_pad_16:
  b:seq U8.t{length b < pow2 32} ->
  len_16:nat{len_16 = 16 * (length b / 16)} ->
  rem_16:nat{rem_16 = length b % 16} ->
  Lemma (
    len_16 <= length b /\ rem_16 + len_16 = length b /\
    (let x = slice b 0 len_16 in let y = slice b len_16 (length b) in
     if rem_16 = 0 then encode_bytes (pad_16 b) == encode_bytes x
     else (length (pad_16 y) = 16
           /\ encode_bytes (pad_16 b) == Seq.cons (pad_16 y) (encode_bytes x))))
let lemma_pad_16 b len_16 rem_16 =
  if rem_16 = 0 then Seq.lemma_eq_intro (slice b 0 (len_16)) b
  else (
    let x = slice b 0 len_16 in
    let y = slice b len_16 (length b) in
    Seq.lemma_eq_intro (slice (pad_16 b) 0 len_16) x;
    Seq.lemma_eq_intro (slice (pad_16 b) len_16 (length (pad_16 b))) (pad_16 y);
    Seq.lemma_eq_intro (pad_16 b) (slice (pad_16 b) 0 len_16 @| slice (pad_16 b) len_16 (length (pad_16 b)));
    Seq.lemma_eq_intro (pad_16 b) (x @| pad_16 y);
    encode_bytes_append (length x) x (pad_16 y);
    Seq.lemma_eq_intro (encode_bytes (x @| pad_16 y)) (Seq.cons (pad_16 y) (encode_bytes x));
    Seq.lemma_eq_intro (encode_bytes (pad_16 b)) (Seq.cons (pad_16 y) (encode_bytes x))
  )

