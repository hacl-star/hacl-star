module Lib.Bitmap

open Lib.Sliceable

module IT = Lib.IntTypes

#set-options "--fuel 0 --ifuel 0"

inline_for_extraction noextract val uN (t:IT.inttype{IT.unsigned t}) (l:IT.secrecy_level) : (xN:sig (IT.bits t){xN.t == IT.int_t t l})
inline_for_extraction noextract
let uN t l =
{ t = IT.int_t t l
; v = (fun x i -> FStar.UInt.nth #(IT.bits t) (IT.v x) i)
; mk = (fun f -> IT.mk_int (UInt.from_vec #(IT.bits t) (FStar.Seq.init (IT.bits t) f)))
; mk_def = (fun f i -> ())
; ones_ = IT.ones t l
; zeros_ = IT.zeros t l
; and_ = IT.logand
; xor_ = IT.logxor
; or_ = IT.logor
; not_ = IT.lognot
; zeros_spec = (fun i -> UInt.zero_nth_lemma #(IT.bits t) i)
; ones_spec = (fun i -> UInt.ones_nth_lemma #(IT.bits t) i)
; and_spec = (fun x y i -> IT.logand_spec x y)
; xor_spec = (fun x y i -> IT.logxor_spec x y)
; or_spec = (fun x y i -> IT.logor_spec x y)
; not_spec = (fun x i -> IT.lognot_spec x)
}

inline_for_extraction noextract
val uN_eq
  (#t1 #t2:(t:IT.inttype{IT.unsigned t})) (#l:IT.secrecy_level)
  (x:(uN t1 l).t) (y:(uN t2 l).t) : Type0
inline_for_extraction noextract
let uN_eq x y = forall i. (_).v x i == (_).v y i

inline_for_extraction noextract
val uN_shift_left
  (#t:IT.inttype{IT.unsigned t}) (#l:IT.secrecy_level)
  (x:(uN t l).t) (k:nat{k<IT.bits t}) :
  Pure (uN t l).t
    (requires True)
    (ensures fun y -> forall (i:nat{i<IT.bits t-k}). (_).v y i == (_).v x (i+k))
inline_for_extraction noextract
let uN_shift_left #t #l x k =
  let y : (uN t l).t = IT.shift_left #t #l x (IT.size k) in
  let aux (i:nat{i<IT.bits t-k}) : Lemma ((_).v y i == (_).v x (i+k)) =
    if IT.bits t=0 then
      ()
    else
      FStar.UInt.shift_left_lemma_2 #(IT.bits t) (IT.v #t #l x) k i
  in
  FStar.Classical.forall_intro aux;
  y

inline_for_extraction noextract
val uN_shift_right
  (#t:IT.inttype{IT.unsigned t}) (#l:IT.secrecy_level) (#n:nat{n<=IT.bits t})
  (x:(uN t l).t) (k:nat{k<IT.bits t}) :
  Pure (uN t l).t
    (requires True)
    (ensures fun y -> forall (i:nat{i<n}). (_).v y i == (if i<k then false else (_).v x (i-k)))
inline_for_extraction noextract
let uN_shift_right #t #l #n x k =
  let y : (uN t l).t = IT.shift_right #t #l x (IT.size k) in
  let aux (i:nat{i<n}) : Lemma ((_).v y i == (if i<k then false else (_).v x (i-k))) =
    if n=0 then (
      ()
    ) else if i<k then (
      FStar.UInt.shift_right_lemma_1 #(IT.bits t) (IT.v #t #l x) k i
    ) else (
      FStar.UInt.shift_right_lemma_2 #(IT.bits t) (IT.v #t #l x) k i
    )
  in
  FStar.Classical.forall_intro aux;
  y

inline_for_extraction noextract
let uNxM (t:IT.inttype{IT.unsigned t}) (l:IT.secrecy_level) (m:IT.size_nat) : Type0 =
  xNxM (uN t l) m
