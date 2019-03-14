module Hacl.Bignum25519

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

#reset-options "--max_fuel 0 --z3rlimit 20"

open FStar.Buffer


(* Type abbreviations *)
let limb  = Hacl.UInt64.t
let felem = b:Buffer.buffer limb{Buffer.length b = 5}
let seqelem = b:Seq.seq limb{Seq.length b = 5}

(* Bound conditions *)
val red_51: seqelem -> GTot Type0
val red_513: seqelem -> GTot Type0
val red_53: seqelem -> GTot Type0
val red_5413: seqelem -> GTot Type0
val red_55: seqelem -> GTot Type0

(* Bound lemmas *)
val lemma_red_51_is_red_513: s:seqelem -> Lemma (requires (red_51 s))
                                                                       (ensures (red_513 s))
val lemma_red_51_is_red_53: s:seqelem -> Lemma (requires (red_51 s))
                                                                       (ensures (red_53 s))
val lemma_red_51_is_red_5413: s:seqelem -> Lemma (requires (red_51 s))
                                                                       (ensures (red_5413 s))
val lemma_red_51_is_red_55: s:seqelem -> Lemma (requires (red_51 s))
                                                                       (ensures (red_55 s))
val lemma_red_513_is_red_53: s:seqelem -> Lemma (requires (red_513 s))
                                                                       (ensures (red_53 s))
val lemma_red_513_is_red_5413: s:seqelem -> Lemma (requires (red_513 s))
                                                                       (ensures (red_5413 s))
val lemma_red_513_is_red_55: s:seqelem -> Lemma (requires (red_513 s))
                                                                       (ensures (red_55 s))
val lemma_red_53_is_red_5413: s:seqelem -> Lemma (requires (red_53 s))
                                                                       (ensures (red_5413 s))
val lemma_red_53_is_red_55: s:seqelem -> Lemma (requires (red_53 s))
                                                                       (ensures (red_55 s))
val lemma_red_5413_is_red_55: s:seqelem -> Lemma (requires (red_5413 s))
                                                                       (ensures (red_55 s))


(* Functional mapping to mathematical integers *)
val seval: seqelem -> GTot Spec.Curve25519.elem

inline_for_extraction
val fsum:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_53 (as_seq h1 a)
      /\ seval (as_seq h1 a) == Spec.Curve25519.fadd (seval (as_seq h0 a)) (seval (as_seq h0 b))))
  
inline_for_extraction
val fdifference:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_5413 (as_seq h1 a)
      /\ seval (as_seq h1 a) == Spec.Curve25519.fsub (seval (as_seq h0 b)) (seval (as_seq h0 a))))

inline_for_extraction
val reduce_513:
  a:felem -> 
  Stack unit
    (requires (fun h -> live h a /\ red_5413 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 a /\ red_5413 (as_seq h0 a)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_513 (as_seq h1 a)
      /\ seval (as_seq h1 a) == seval (as_seq h0 a)))

inline_for_extraction
val fdifference_reduced:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_513 (as_seq h1 a)
      /\ seval (as_seq h1 a) == Spec.Curve25519.fsub (seval (as_seq h0 b)) (seval (as_seq h0 a))))

inline_for_extraction
val fmul:
  out:felem ->
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ live h b /\ red_53 (as_seq h a) /\ red_5413 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ live h0 b /\ red_53 (as_seq h0 a) /\ red_5413 (as_seq h0 b) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.fmul (seval (as_seq h0 a)) (seval (as_seq h0 b))))

inline_for_extraction
val times_2:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a)
      /\ live h1 out /\ modifies_1 out h0 h1 /\ red_53 (as_seq h1 out)
      /\ seval (as_seq h1 out) == Spec.Curve25519.fmul 2 (seval (as_seq h0 a))))

inline_for_extraction
val times_d:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a)
      /\ live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out)
      /\ seval (as_seq h1 out) == Spec.Curve25519.fmul Spec.Ed25519.d (seval (as_seq h0 a))))

inline_for_extraction
val times_2d:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a)
      /\ live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out)
      /\ seval (as_seq h1 out) == Spec.Curve25519.(2 `fmul` Spec.Ed25519.d `fmul` (seval (as_seq h0 a)))))

inline_for_extraction
val fsquare:
  out:felem ->
  a:felem{disjoint a out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_5413 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_5413 (as_seq h0 a) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.fmul (seval (as_seq h0 a)) (seval (as_seq h0 a))))

inline_for_extraction
val fsquare_times:
  out:felem ->
  a:felem{disjoint out a} ->
  n:FStar.UInt32.t{FStar.UInt32.v n > 0} ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_5413 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_5413 (as_seq h0 a) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.op_Star_Star (seval (as_seq h0 a)) (pow2 (FStar.UInt32.v n))))

inline_for_extraction
val fsquare_times_inplace:
  out:felem ->
  n:FStar.UInt32.t{FStar.UInt32.v n > 0} ->
  Stack unit
    (requires (fun h -> live h out /\ red_5413 (as_seq h out)))
    (ensures (fun h0 _ h1 -> live h0 out /\ red_5413 (as_seq h0 out) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.((seval (as_seq h0 out)) ** (pow2 (FStar.UInt32.v n)))))

inline_for_extraction
val inverse:
  out:felem ->
  a:felem{disjoint a out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Ed25519.modp_inv (seval (as_seq h0 a))))

inline_for_extraction
val reduce:
  out:felem ->
  Stack unit
    (requires (fun h -> live h out /\ red_513 (as_seq h out)))
    (ensures (fun h0 _ h1 -> live h0 out /\ red_513 (as_seq h0 out) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_51 (as_seq h1 out) /\
      (let s = as_seq h1 out in
       FStar.Mul.(Hacl.UInt64.(v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4) < Spec.Curve25519.prime))) /\
      seval (as_seq h1 out) == seval (as_seq h0 out)))

inline_for_extraction
val lemma_reveal_red_51: s:seqelem ->
  Lemma (requires (red_51 s))
        (ensures (let open Hacl.UInt64 in
         v (Seq.index s 0) < pow2 51 /\ v (Seq.index s 1) < pow2 51 /\
         v (Seq.index s 2) < pow2 51 /\ v (Seq.index s 3) < pow2 51 /\
         v (Seq.index s 4) < pow2 51))

inline_for_extraction
val lemma_intro_red_51: s:seqelem ->
  Lemma (requires (let open Hacl.UInt64 in
         v (Seq.index s 0) < pow2 51 /\ v (Seq.index s 1) < pow2 51 /\
         v (Seq.index s 2) < pow2 51 /\ v (Seq.index s 3) < pow2 51 /\
         v (Seq.index s 4) < pow2 51))
        (ensures (red_51 s))

inline_for_extraction
val lemma_reveal_red_513: s:seqelem ->
  Lemma (requires (red_513 s))
        (ensures (let open Hacl.UInt64 in
         v (Seq.index s 0) < pow2 51 + pow2 13 /\ v (Seq.index s 1) < pow2 51 + pow2 13 /\
         v (Seq.index s 2) < pow2 51 + pow2 13 /\ v (Seq.index s 3) < pow2 51 + pow2 13 /\
         v (Seq.index s 4) < pow2 51 + pow2 13))

inline_for_extraction
val lemma_intro_red_513: s:seqelem ->
  Lemma (requires (let open Hacl.UInt64 in
         v (Seq.index s 0) < pow2 51 + pow2 13 /\ v (Seq.index s 1) < pow2 51 + pow2 13 /\
         v (Seq.index s 2) < pow2 51 + pow2 13 /\ v (Seq.index s 3) < pow2 51 + pow2 13 /\
         v (Seq.index s 4) < pow2 51 + pow2 13))
        (ensures (red_513 s))

inline_for_extraction
val lemma_reveal_seval: s:seqelem ->
  Lemma (FStar.Mul.(Hacl.UInt64.((v (Seq.index s 0)
                               + pow2 51 * v (Seq.index s 1)
                               + pow2 102 * v (Seq.index s 2)
                               + pow2 153 * v (Seq.index s 3)
                               + pow2 204 * v (Seq.index s 4)) % (pow2 255 - 19) == seval s)))
