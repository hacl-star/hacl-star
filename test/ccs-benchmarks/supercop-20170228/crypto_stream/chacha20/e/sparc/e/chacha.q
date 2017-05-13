# 20080118
# D. J. Bernstein
# Public domain.

int64 x
int64 arg2
int64 arg3
int64 arg4

input x
input arg2
input arg3
input arg4

int64 i
int64 a
int64 m
int64 out
int64 bytes
stack64 ctarget
stack512 tmp

stack64 bytes_stack
stack64 out_stack
stack64 m_stack
stack64 x_stack

int64 z0
int64 z1
int64 z2
int64 z3
int64 z4
int64 z5
int64 z6
int64 z7
int64 z8
int64 z9
int64 z10
int64 z11
int64 z12
int64 z13
int64 z14
int64 z15

int64 u0
int64 u1
int64 u2
int64 u3
int64 u4
int64 u5
int64 u6
int64 u7
int64 u8
int64 u9
int64 u10
int64 u11
int64 u12
int64 u13
int64 u14
int64 u15

int64 y0
int64 y1
int64 y2
int64 y3
int64 y4
int64 y5
int64 y6
int64 y7
int64 y8
int64 y9
int64 y10
int64 y11
int64 y12
int64 y13
int64 y14
int64 y15

int64 x0
int64 x1
int64 x2
int64 x3
int64 x4
int64 x5
int64 x6
int64 x7
int64 x8
int64 x9
int64 x10
int64 x11
int64 x12
int64 x13
int64 x14
int64 x15

int64 q0
int64 q1
int64 q2
int64 q3
int64 q4
int64 q5
int64 q6
int64 q7
int64 q8
int64 q9
int64 q10
int64 q11
int64 q12
int64 q13
int64 q14
int64 q15

int64 m0
int64 m1
int64 m2
int64 m3
int64 m4
int64 m5
int64 m6
int64 m7
int64 m8
int64 m9
int64 m10
int64 m11
int64 m12
int64 m13
int64 m14
int64 m15

enter ECRYPT_keystream_bytes

bytes = arg3
m = arg2
out = arg2

              unsigned>? bytes - 0
goto done if !unsigned>

  a = 0
  i = bytes
  zeroloop:
    *(int8 *) (out + 0) = a
    out += 1
                   unsigned>? i -= 1
  goto zeroloop if unsigned>
  out -= bytes

goto bytesatleast1

enter ECRYPT_decrypt_bytes

bytes = arg4
m = arg2
out = arg3

              unsigned>? bytes - 0
goto done if !unsigned>
goto bytesatleast1

enter ECRYPT_encrypt_bytes

bytes = arg4
m = arg2
out = arg3

              unsigned>? bytes - 0
goto done if !unsigned>
bytesatleast1:

                          unsigned<? bytes - 64
  goto bytesatleast64 if !unsigned<

    ctarget = out
    out = &tmp
    i = 0
    mcopyloop:
      a = *(int8 *) (m + i)
      *(int8 *) (out + i) = a
      i += 1
                      unsigned<? i - bytes
    goto mcopyloop if unsigned<
    m = &tmp

  bytesatleast64:

    x0 = *(uint32 *) (x + 0)
    x1 = *(uint32 *) (x + 4)
    x2 = *(uint32 *) (x + 8)
    x3 = *(uint32 *) (x + 12)
    x4 = *(uint32 *) (x + 16)
    x5 = *(uint32 *) (x + 20)
    x6 = *(uint32 *) (x + 24)
    x7 = *(uint32 *) (x + 28)
    x8 = *(uint32 *) (x + 32)
    x9 = *(uint32 *) (x + 36)
    x10 = *(uint32 *) (x + 40)
    x11 = *(uint32 *) (x + 44)
    x12 = *(uint32 *) (x + 48)
    x13 = *(uint32 *) (x + 52)
    x14 = *(uint32 *) (x + 56)
    x15 = *(uint32 *) (x + 60)

    i = 20

    bytes_stack = bytes
    out_stack = out
    m_stack = m
    x_stack = x

    mainloop:


x0 += x4
                x1 += x5
x12 ^= x0
                                x2 += x6
z12 = (uint32) x12 << 16
                x13 ^= x1
x12 = (uint32) x12 >> 16
                                x14 ^= x2
                z13 = (uint32) x13 << 16
x12 |= z12
		x13 = (uint32) x13 >> 16
                                                x3 += x7
                                z14 = (uint32) x14 << 16
                                                x15 ^= x3
				x14 = (uint32) x14 >> 16
		x13 |= z13
                                                z15 = (uint32) x15 << 16
				x14 |= z14
						x15 = (uint32) x15 >> 16
x8 += x12
						x15 |= z15
                x9 += x13
x4 ^= x8
                                x10 += x14
z4 = (uint32) x4 << 12
                x5 ^= x9
x4 = (uint32) x4 >> 20
                                x6 ^= x10
                z5 = (uint32) x5 << 12
x4 |= z4
		x5 = (uint32) x5 >> 20
                                                x11 += x15
                                z6 = (uint32) x6 << 12
                                                x7 ^= x11
				x6 = (uint32) x6 >> 20
		x5 |= z5
                                                z7 = (uint32) x7 << 12
				x6 |= z6
						x7 = (uint32) x7 >> 20
x0 += x4
						x7 |= z7
                x1 += x5
x12 ^= x0
                                x2 += x6
z12 = (uint32) x12 << 8
                x13 ^= x1
x12 = (uint32) x12 >> 24
                                x14 ^= x2
                z13 = (uint32) x13 << 8
x12 |= z12
		x13 = (uint32) x13 >> 24
                                                x3 += x7
                                z14 = (uint32) x14 << 8
                                                x15 ^= x3
				x14 = (uint32) x14 >> 24
		x13 |= z13
                                                z15 = (uint32) x15 << 8
				x14 |= z14
						x15 = (uint32) x15 >> 24
x8 += x12
						x15 |= z15
                x9 += x13
x4 ^= x8
                                x10 += x14
z4 = (uint32) x4 << 7
                x5 ^= x9
x4 = (uint32) x4 >> 25
                                x6 ^= x10
                z5 = (uint32) x5 << 7
x4 |= z4
		x5 = (uint32) x5 >> 25
                                                x11 += x15
                                z6 = (uint32) x6 << 7
                                                x7 ^= x11
				x6 = (uint32) x6 >> 25
		x5 |= z5
                                                z7 = (uint32) x7 << 7
				x6 |= z6
						x7 = (uint32) x7 >> 25
x0 += x5
						x7 |= z7
                x1 += x6
x15 ^= x0
                                x2 += x7
z15 = (uint32) x15 << 16
                x12 ^= x1
x15 = (uint32) x15 >> 16
                                x13 ^= x2
                z12 = (uint32) x12 << 16
x15 |= z15
		x12 = (uint32) x12 >> 16
                                                x3 += x4
                                z13 = (uint32) x13 << 16
                                                x14 ^= x3
				x13 = (uint32) x13 >> 16
		x12 |= z12
                                                z14 = (uint32) x14 << 16
				x13 |= z13
						x14 = (uint32) x14 >> 16
x10 += x15
						x14 |= z14
                x11 += x12
x5 ^= x10
                                x8 += x13
z5 = (uint32) x5 << 12
                x6 ^= x11
x5 = (uint32) x5 >> 20
                                x7 ^= x8
                z6 = (uint32) x6 << 12
x5 |= z5
		x6 = (uint32) x6 >> 20
                                                x9 += x14
                                z7 = (uint32) x7 << 12
                                                x4 ^= x9
				x7 = (uint32) x7 >> 20
		x6 |= z6
                                                z4 = (uint32) x4 << 12
				x7 |= z7
						x4 = (uint32) x4 >> 20
x0 += x5
						x4 |= z4
                x1 += x6
x15 ^= x0
                                x2 += x7
z15 = (uint32) x15 << 8
                x12 ^= x1
x15 = (uint32) x15 >> 24
                                x13 ^= x2
                z12 = (uint32) x12 << 8
x15 |= z15
		x12 = (uint32) x12 >> 24
                                                x3 += x4
                                z13 = (uint32) x13 << 8
                                                x14 ^= x3
				x13 = (uint32) x13 >> 24
		x12 |= z12
                                                z14 = (uint32) x14 << 8
				x13 |= z13
						x14 = (uint32) x14 >> 24
x10 += x15
						x14 |= z14
                x11 += x12
x5 ^= x10
                                x8 += x13
z5 = (uint32) x5 << 7
                x6 ^= x11
x5 = (uint32) x5 >> 25
                                x7 ^= x8
                z6 = (uint32) x6 << 7
x5 |= z5
		x6 = (uint32) x6 >> 25
                                                x9 += x14
                                z7 = (uint32) x7 << 7
                                                x4 ^= x9
				x7 = (uint32) x7 >> 25
		x6 |= z6
                                                z4 = (uint32) x4 << 7
				x7 |= z7
						x4 = (uint32) x4 >> 25
                 unsigned>? i -= 2
						x4 |= z4
goto mainloop if unsigned>

  x = x_stack

  q0 = *(uint32 *) (x + 0)
  q1 = *(uint32 *) (x + 4)
  q2 = *(uint32 *) (x + 8)
  q3 = *(uint32 *) (x + 12)
  x0 += q0
  q4 = *(uint32 *) (x + 16)
  x1 += q1
  q5 = *(uint32 *) (x + 20)
  x2 += q2
  q6 = *(uint32 *) (x + 24)
  x3 += q3
  q7 = *(uint32 *) (x + 28)
  x4 += q4
  q8 = *(uint32 *) (x + 32)
  x5 += q5
  q9 = *(uint32 *) (x + 36)
  x6 += q6
  q10 = *(uint32 *) (x + 40)
  x7 += q7
  q11 = *(uint32 *) (x + 44)
  x8 += q8
  q12 = *(uint32 *) (x + 48)
  x9 += q9
  q13 = *(uint32 *) (x + 52)
  x10 += q10
  q14 = *(uint32 *) (x + 56)
  x11 += q11
  q15 = *(uint32 *) (x + 60)
  x12 += q12
  q12 += 1
  *(uint32 *) (x + 48) = q12
  q12 = (uint64) q12 >> 32
  x13 += q13
  q13 += q12
  *(uint32 *) (x + 52) = q13
  x14 += q14
  x15 += q15

  m = m_stack

  m0 = *(swapendian uint32 *) m
  m += 4
  m1 = *(swapendian uint32 *) m
  m += 4
  m2 = *(swapendian uint32 *) m
  m += 4
  m3 = *(swapendian uint32 *) m
  m += 4
  x0 ^= m0
  m4 = *(swapendian uint32 *) m
  m += 4
  x1 ^= m1
  m5 = *(swapendian uint32 *) m
  m += 4
  x2 ^= m2
  m6 = *(swapendian uint32 *) m
  m += 4
  x3 ^= m3
  m7 = *(swapendian uint32 *) m
  m += 4
  x4 ^= m4
  m8 = *(swapendian uint32 *) m
  m += 4
  x5 ^= m5
  m9 = *(swapendian uint32 *) m
  m += 4
  x6 ^= m6
  m10 = *(swapendian uint32 *) m
  m += 4
  x7 ^= m7
  m11 = *(swapendian uint32 *) m
  m += 4
  x8 ^= m8
  m12 = *(swapendian uint32 *) m
  m += 4
  x9 ^= m9
  m13 = *(swapendian uint32 *) m
  m += 4
  x10 ^= m10
  m14 = *(swapendian uint32 *) m
  m += 4
  x11 ^= m11
  m15 = *(swapendian uint32 *) m
  m += 4
  x12 ^= m12
  x13 ^= m13
  x14 ^= m14
  x15 ^= m15

  out = out_stack
  *(swapendian uint32 *) out = x0
  out += 4
  *(swapendian uint32 *) out = x1
  out += 4
  *(swapendian uint32 *) out = x2
  out += 4
  *(swapendian uint32 *) out = x3
  out += 4
  *(swapendian uint32 *) out = x4
  out += 4
  *(swapendian uint32 *) out = x5
  out += 4
  *(swapendian uint32 *) out = x6
  out += 4
  *(swapendian uint32 *) out = x7
  out += 4
  *(swapendian uint32 *) out = x8
  out += 4
  *(swapendian uint32 *) out = x9
  out += 4
  *(swapendian uint32 *) out = x10
  out += 4
  *(swapendian uint32 *) out = x11
  out += 4
  *(swapendian uint32 *) out = x12
  out += 4
  *(swapendian uint32 *) out = x13
  out += 4
  *(swapendian uint32 *) out = x14
  out += 4
  *(swapendian uint32 *) out = x15
  out += 4

  bytes = bytes_stack
                        unsigned>? bytes -= 64
  goto bytesatleast1 if unsigned>
  goto done if !unsigned<

    m = ctarget
    bytes += 64
    out -= 64
    i = 0
    ccopyloop:
      a = *(int8 *) (out + i)
      *(int8 *) (m + i) = a
      i += 1
                      unsigned<? i - bytes
    goto ccopyloop if unsigned<

done:
leave


enter ECRYPT_init
leave


enter ECRYPT_ivsetup
  x14 = *(uint32 *) (arg2 + 0)
  x12 = 0
  x15 = *(uint32 *) (arg2 + 4)
  x13 = 0
  x += 48
  *(int32 *) (x + 0) = x12
  x += 4
  *(int32 *) (x + 0) = x13
  x += 4
  *(swapendian int32 *) x = x14
  x += 4
  *(swapendian int32 *) x = x15
leave


enter ECRYPT_keysetup

                 unsigned>? arg3 - 128
goto kbits256 if unsigned>

kbits128:

  x4 = *(uint32 *) (arg2 + 0)
  x0 = 1634760805 & 0xfffffc00
  x5 = *(uint32 *) (arg2 + 4)
  x1 = 824206446 & 0xfffffc00
  x6 = *(uint32 *) (arg2 + 8)
  x2 = 2036477238 & 0xfffffc00
  x7 = *(uint32 *) (arg2 + 12)
  x3 = 1797285236 & 0xfffffc00
  x8 = x4
  x0 |= 1634760805 & 0x3ff
  x9 = x5
  x1 |= 824206446 & 0x3ff
  x10 = x6
  x2 |= 2036477238 & 0x3ff
  x11 = x7
  x3 |= 1797285236 & 0x3ff

goto storekey

kbits256:

  x4 = *(uint32 *) (arg2 + 0)
  x0 = 1634760805 & 0xfffffc00
  x5 = *(uint32 *) (arg2 + 4)
  x1 = 857760878 & 0xfffffc00
  x6 = *(uint32 *) (arg2 + 8)
  x2 = 2036477234 & 0xfffffc00
  x7 = *(uint32 *) (arg2 + 12)
  x3 = 1797285236 & 0xfffffc00
  x8 = *(uint32 *) (arg2 + 16)
  x0 |= 1634760805 & 0x3ff
  x9 = *(uint32 *) (arg2 + 20)
  x1 |= 857760878 & 0x3ff
  x10 = *(uint32 *) (arg2 + 24)
  x2 |= 2036477234 & 0x3ff
  x11 = *(uint32 *) (arg2 + 28)
  x3 |= 1797285236 & 0x3ff

storekey:

  *(int32 *) (x + 0) = x0
  x += 4
  *(int32 *) (x + 0) = x1
  x += 4
  *(int32 *) (x + 0) = x2
  x += 4
  *(int32 *) (x + 0) = x3
  x += 4
  *(swapendian int32 *) x = x4
  x += 4
  *(swapendian int32 *) x = x5
  x += 4
  *(swapendian int32 *) x = x6
  x += 4
  *(swapendian int32 *) x = x7
  x += 4
  *(swapendian int32 *) x = x8
  x += 4
  *(swapendian int32 *) x = x9
  x += 4
  *(swapendian int32 *) x = x10
  x += 4
  *(swapendian int32 *) x = x11

leave


