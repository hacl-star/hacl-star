module Hacl.Bignum25519

#reset-options "--max_fuel 0 --z3rlimit 20"

open FStar.Buffer

let limb  = Hacl.UInt64.t
let felem = b:Buffer.buffer limb{Buffer.length b = 5}
let seqelem = b:Seq.seq limb{Seq.length b = 5}

val red_51: seqelem -> GTot Type0
val red_513: seqelem -> GTot Type0
val red_53: seqelem -> GTot Type0
val red_5413: seqelem -> GTot Type0


val seval: seqelem -> GTot Spec.Curve25519.elem


val fsum:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_53 (as_seq h1 a)
      /\ seval (as_seq h1 a) == Spec.Curve25519.fadd (seval (as_seq h0 a)) (seval (as_seq h0 b))))
  

val fdifference:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_5413 (as_seq h1 a)
      /\ seval (as_seq h1 a) == Spec.Curve25519.fsub (seval (as_seq h0 b)) (seval (as_seq h0 a))))


val reduce_513:
  a:felem -> 
  Stack unit
    (requires (fun h -> live h a /\ red_5413 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 a /\ red_5413 (as_seq h0 a)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_513 (as_seq h1 a)
      /\ seval (as_seq h1 a) == seval (as_seq h0 a)))


val fdifference_reduced:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ red_513 (as_seq h a) /\ red_513 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ red_513 (as_seq h0 a) /\ red_513 (as_seq h0 b)
      /\ live h1 a /\ modifies_1 a h0 h1 /\ red_513 (as_seq h1 a)
      /\ seval (as_seq h1 a) == Spec.Curve25519.fsub (seval (as_seq h0 b)) (seval (as_seq h0 a))))

val fmul:
  out:felem ->
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ live h b /\ red_53 (as_seq h a) /\ red_5413 (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ live h0 b /\ red_53 (as_seq h0 a) /\ red_5413 (as_seq h0 b) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.fmul (seval (as_seq h0 a)) (seval (as_seq h0 b))))

val times_2:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a)
      /\ live h1 out /\ modifies_1 out h0 h1 /\ red_53 (as_seq h1 out)
      /\ seval (as_seq h1 out) == Spec.Curve25519.fmul 2 (seval (as_seq h0 a))))


val times_d:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a)
      /\ live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out)
      /\ seval (as_seq h1 out) == Spec.Curve25519.fmul Spec.Ed25519.d (seval (as_seq h0 a))))


val times_2d:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a)
      /\ live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out)
      /\ seval (as_seq h1 out) == Spec.Curve25519.(2 `fmul` Spec.Ed25519.d `fmul` (seval (as_seq h0 a)))))


val fsquare:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.fmul (seval (as_seq h0 a)) (seval (as_seq h0 a))))


val fsquare_times:
  out:felem ->
  a:felem ->
  n:UInt32.t ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.((seval (as_seq h0 a)) ** (pow2 (UInt32.v n)))))


val fsquare_times_inplace:
  out:felem ->
  n:UInt32.t ->
  Stack unit
    (requires (fun h -> live h out /\ red_513 (as_seq h out)))
    (ensures (fun h0 _ h1 -> live h0 out /\ red_513 (as_seq h0 out) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Curve25519.((seval (as_seq h0 out)) ** (pow2 (UInt32.v n)))))


val inverse:
  out:felem ->
  a:felem ->
  Stack unit
    (requires (fun h -> live h out /\ live h a /\ red_513 (as_seq h a)))
    (ensures (fun h0 _ h1 -> live h0 out /\ live h0 a /\ red_513 (as_seq h0 a) /\
      live h1 out /\ modifies_1 out h0 h1 /\ red_513 (as_seq h1 out) /\
      seval (as_seq h1 out) == Spec.Ed25519.modp_inv (seval (as_seq h0 a))))


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
                               + pow2 204 * v (Seq.index s 4) == seval (as_seq h0 out))))))
