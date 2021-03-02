module Hacl.Impl.EC.P521.Reduction

(* INPUT: An integer c = (c1041,..., c2, c1, c0) in base 2 with 0 ≤ c < p2
521.
OUTPUT: c mod p521.
1. Define 521-bit integers:
s1 = (c1041,..., c523, c522, c521),
s2 = (c520,..., c2, c1, c0).
2. Return(s1 +s2 mod p521). *)