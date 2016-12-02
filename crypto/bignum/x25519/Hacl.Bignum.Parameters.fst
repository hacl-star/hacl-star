module Hacl.Bignum.Parameters

open FStar.HyperStack
open FStar.Buffer

let prime =
  assert_norm (pow2 255 > 19);
  pow2 255 - 19

let word_size = 64

inline_for_extraction let limb = Hacl.UInt64.t
inline_for_extraction let wide = Hacl.UInt128.t

let v x = Hacl.UInt64.v x
let w x = Hacl.UInt128.v x

let len = 5
inline_for_extraction let clen = 5ul

let limb_size = 51
inline_for_extraction let climb_size = 51ul

let reduced_after_mul h b =
  let _ = 0 in
  live h b /\ v (get h b 0) < pow2 52 /\ v (get h b 1) < pow2 52 /\ v (get h b 2) < pow2 52
  /\ v (get h b 3) < pow2 52 /\ v (get h b 4) < pow2 52

let reduced_before_mul_l h b =
  let _ = 0 in
  live h b /\ v (get h b 0) < pow2 53 /\ v (get h b 1) < pow2 53 /\ v (get h b 2) < pow2 53
  /\ v (get h b 3) < pow2 53 /\ v (get h b 4) < pow2 53

let reduced_before_mul_r h b =
  let _ = 0 in
  live h b /\ v (get h b 0) < pow2 54 /\ v (get h b 1) < pow2 54 /\ v (get h b 2) < pow2 54
  /\ v (get h b 3) < pow2 54 /\ v (get h b 4) < pow2 54

let reduced_wide h b =
  let _ = 0 in
  live h b /\ w (get h b 0) < pow2 52 /\ w (get h b 1) < pow2 52 /\ w (get h b 2) < pow2 52
  /\ w (get h b 3) < pow2 52 /\ w (get h b 4) < pow2 52

let reducible h b =
  (* TODO *)
  admit()
