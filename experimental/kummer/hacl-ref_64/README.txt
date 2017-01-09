
We can do kummer fmul in 4M + 4A + 2a
Where M = mul_wide, A = 128-bit add, a = 64-bit add


represent element as 2 64-bit integers: ab, cd.
shift-reduce ab = ba.

4M calculate: ad  bd
              cb  ca

A r1 = ad + cb (<= 2^128 - 2^65 - 2^64 + 1)

A r1 += top 64-bits of bd (<= 2^128 - 2^65)

A r0 = ca + bottom 64-bits of bd (<= 2^126)

A r0 += top 65-bits of r1 (<= 2^126 + 2^65 - 1)

a r1 = bottom 63-bits of r1 + top 62-bits of r0 (<= 2 ^ 64)
a r0 = r0 + top bit of r1
  r1 = bottom 63_bits of r1

For squaring, we can simplify the above to 3M + 3A + 1shl + 2a

3M calculate: ab  bb
                  aa

shl r1 = ab << 1 (<= 2^128 - 2^65 - 2^64 + 1)

A r1 += top 64-bits of bd (<= 2^128 - 2^65)

A r0 = ca + bottom 64-bits of bd (<= 2^126)

A r0 += top 65-bits of r1 (<= 2^126 + 2^65 - 1)

a r1 = bottom 63-bits of r1 + top 62-bits of r0 (<= 2 ^ 63 - 1 | 2 ^ 62 - 1)
a r0 += top bit of r1
  r1 = bottom 63-bits of r1

