# 20080118
# D. J. Bernstein
# Public domain.

int64 a
int64 b
int64 c
int64 d
int64 zero

int64 arg1
int64 arg2
int64 arg3
int64 arg4
input arg1
input arg2
input arg3
input arg4

int64 r11
int64 r12
int64 r13
int64 r14
int64 r15
int64 rbx
int64 rbp
caller r11
caller r12
caller r13
caller r14
caller r15
caller rbx
caller rbp
stack64 r11_stack
stack64 r12_stack
stack64 r13_stack
stack64 r14_stack
stack64 r15_stack
stack64 rbx_stack
stack64 rbp_stack


int64 k
int64 kbits
int64 iv

stack64 i_backup
int64 i

stack64 x_backup
int64 x
stack64 m_backup
int64 m
stack64 out_backup
int64 out
stack64 bytes_backup
int64 bytes

int64 in0
int64 in1
int64 in2
int64 in3
int64 in4
int64 in6
int64 in8
int64 in10
int64 in12
int64 in14

int64 out0
int64 out2
int64 out4
int64 out6
int64 out8
int64 out10
int64 out12
int64 out14

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

stack64 x9_stack
stack64 x11_stack

stack64 j0
stack64 j2
stack64 j4
stack64 j6
stack64 j8
stack64 j10
stack64 j12
stack64 j14

stack512 tmp

stack64 ctarget


enter ECRYPT_keystream_bytes

x = arg1
m = arg2
out = m
bytes = arg3

              unsigned>? bytes - 0
goto done if !unsigned>

zero = 0
i = bytes
while (i) { *out++ = zero; --i }
out -= bytes

goto start


enter ECRYPT_decrypt_bytes

x = arg1
m = arg2
out = arg3
bytes = arg4

              unsigned>? bytes - 0
goto done if !unsigned>

goto start


enter ECRYPT_encrypt_bytes

x = arg1
m = arg2
out = arg3
bytes = arg4

              unsigned>? bytes - 0
goto done if !unsigned>


start:

r11_stack = r11
r12_stack = r12
r13_stack = r13
r14_stack = r14
r15_stack = r15
rbx_stack = rbx
rbp_stack = rbp

in0 = *(uint64 *) (x + 0)
in2 = *(uint64 *) (x + 8)
in4 = *(uint64 *) (x + 16)
in6 = *(uint64 *) (x + 24)
in8 = *(uint64 *) (x + 32)
in10 = *(uint64 *) (x + 40)
in12 = *(uint64 *) (x + 48)
in14 = *(uint64 *) (x + 56)
j0 = in0
j2 = in2
j4 = in4
j6 = in6
j8 = in8
j10 = in10
j12 = in12
j14 = in14

x_backup = x


bytesatleast1:

                  unsigned<? bytes - 64
  goto nocopy if !unsigned<

    ctarget = out

    out = &tmp
    i = bytes
    while (i) { *out++ = *m++; --i }
    out = &tmp
    m = &tmp

  nocopy:

  out_backup = out
  m_backup = m
  bytes_backup = bytes

  x1 = j0
  x0 = x1
  (uint64) x1 >>= 32
  		x3 = j2
  		x2 = x3
  		(uint64) x3 >>= 32
  x5 = j4
  x4 = x5
  (uint64) x5 >>= 32
  		x7 = j6
  		x6 = x7
  		(uint64) x7 >>= 32
  x9 = j8
  x8 = x9
  (uint64) x9 >>= 32
  x9_stack = x9
  		x11 = j10
  		x10 = x11
  		(uint64) x11 >>= 32
		x11_stack = x11
  x13 = j12
  x12 = x13
  (uint64) x13 >>= 32
  		x15 = j14
  		x14 = x15
  		(uint64) x15 >>= 32

  i = 20
  mainloop:
  i_backup = i
		x9 = x9_stack

x0 += x4
x12 ^= x0
(uint32) x12 <<<= 16
  		x1 += x5
  		x13 ^= x1
		(uint32) x13 <<<= 16
x8 += x12
x4 ^= x8
(uint32) x4 <<<= 12
  		x9 += x13
  		x5 ^= x9
		(uint32) x5 <<<= 12
x0 += x4
x12 ^= x0
(uint32) x12 <<<= 8
  		x1 += x5
  		x13 ^= x1
		(uint32) x13 <<<= 8
x8 += x12
x4 ^= x8
(uint32) x4 <<<= 7
  				x2 += x6
  				x14 ^= x2
				(uint32) x14 <<<= 16
  		x9 += x13
  		x5 ^= x9
		(uint32) x5 <<<= 7

		x9_stack = x9

						x11 = x11_stack

  						x3 += x7
  						x15 ^= x3
						(uint32) x15 <<<= 16
  				x10 += x14
  				x6 ^= x10
				(uint32) x6 <<<= 12
  						x11 += x15
  						x7 ^= x11
						(uint32) x7 <<<= 12
  				x2 += x6
  				x14 ^= x2
				(uint32) x14 <<<= 8
  						x3 += x7
  						x15 ^= x3
						(uint32) x15 <<<= 8
  				x10 += x14
  				x6 ^= x10
				(uint32) x6 <<<= 7

  						x11 += x15
  						x7 ^= x11
						(uint32) x7 <<<= 7
x0 += x5
x15 ^= x0
(uint32) x15 <<<= 16

  		x1 += x6
  		x12 ^= x1
		(uint32) x12 <<<= 16
x10 += x15
x5 ^= x10
(uint32) x5 <<<= 12
  		x11 += x12
  		x6 ^= x11
		(uint32) x6 <<<= 12
x0 += x5
x15 ^= x0
(uint32) x15 <<<= 8
  		x1 += x6
  		x12 ^= x1
		(uint32) x12 <<<= 8
x10 += x15
x5 ^= x10
(uint32) x5 <<<= 7
  				x2 += x7
  				x13 ^= x2
				(uint32) x13 <<<= 16
  		x11 += x12
  		x6 ^= x11
		(uint32) x6 <<<= 7

		x11_stack = x11

						x9 = x9_stack

  						x3 += x4
  						x14 ^= x3
						(uint32) x14 <<<= 16
  				x8 += x13
  				x7 ^= x8
				(uint32) x7 <<<= 12
  						x9 += x14
  						x4 ^= x9
						(uint32) x4 <<<= 12
  				x2 += x7
  				x13 ^= x2
				(uint32) x13 <<<= 8
  						x3 += x4
  						x14 ^= x3
						(uint32) x14 <<<= 8
  				x8 += x13
  				x7 ^= x8
				(uint32) x7 <<<= 7
  						x9 += x14
  						x4 ^= x9
						(uint32) x4 <<<= 7

x0 += x4
x12 ^= x0
(uint32) x12 <<<= 16
  		x1 += x5
  		x13 ^= x1
		(uint32) x13 <<<= 16
x8 += x12
x4 ^= x8
(uint32) x4 <<<= 12
  		x9 += x13
  		x5 ^= x9
		(uint32) x5 <<<= 12
x0 += x4
x12 ^= x0
(uint32) x12 <<<= 8
  		x1 += x5
  		x13 ^= x1
		(uint32) x13 <<<= 8
x8 += x12
x4 ^= x8
(uint32) x4 <<<= 7
  				x2 += x6
  				x14 ^= x2
				(uint32) x14 <<<= 16
  		x9 += x13
  		x5 ^= x9
		(uint32) x5 <<<= 7

		x9_stack = x9

						x11 = x11_stack

  						x3 += x7
  						x15 ^= x3
						(uint32) x15 <<<= 16
  				x10 += x14
  				x6 ^= x10
				(uint32) x6 <<<= 12
  						x11 += x15
  						x7 ^= x11
						(uint32) x7 <<<= 12
  				x2 += x6
  				x14 ^= x2
				(uint32) x14 <<<= 8
  						x3 += x7
  						x15 ^= x3
						(uint32) x15 <<<= 8
  				x10 += x14
  				x6 ^= x10
				(uint32) x6 <<<= 7

  						x11 += x15
  						x7 ^= x11
						(uint32) x7 <<<= 7
x0 += x5
x15 ^= x0
(uint32) x15 <<<= 16

  		x1 += x6
  		x12 ^= x1
		(uint32) x12 <<<= 16
x10 += x15
x5 ^= x10
(uint32) x5 <<<= 12
  		x11 += x12
  		x6 ^= x11
		(uint32) x6 <<<= 12
x0 += x5
x15 ^= x0
(uint32) x15 <<<= 8
  		x1 += x6
  		x12 ^= x1
		(uint32) x12 <<<= 8
x10 += x15
x5 ^= x10
(uint32) x5 <<<= 7
  				x2 += x7
  				x13 ^= x2
				(uint32) x13 <<<= 16
  		x11 += x12
  		x6 ^= x11
		(uint32) x6 <<<= 7

		x11_stack = x11

						x9 = x9_stack

  						x3 += x4
  						x14 ^= x3
						(uint32) x14 <<<= 16
  				x8 += x13
  				x7 ^= x8
				(uint32) x7 <<<= 12
  						x9 += x14
  						x4 ^= x9
						(uint32) x4 <<<= 12
  				x2 += x7
  				x13 ^= x2
				(uint32) x13 <<<= 8
  						x3 += x4
  						x14 ^= x3
						(uint32) x14 <<<= 8
  				x8 += x13
  				x7 ^= x8
				(uint32) x7 <<<= 7
  						x9 += x14
  						x4 ^= x9
						(uint32) x4 <<<= 7

		x9_stack = x9
  i = i_backup
                 unsigned>? i -= 4
goto mainloop if unsigned>

  (uint32) x2 += j2
  x3 <<= 32
  x3 += j2
  (uint64) x3 >>= 32
  x3 <<= 32
  x2 += x3

  (uint32) x6 += j6
  x7 <<= 32
  x7 += j6
  (uint64) x7 >>= 32
  x7 <<= 32
  x6 += x7

  x9 = x9_stack

  (uint32) x8 += j8
  x9 <<= 32
  x9 += j8
  (uint64) x9 >>= 32
  x9 <<= 32
  x8 += x9

  (uint32) x12 += j12
  x13 <<= 32
  x13 += j12
  (uint64) x13 >>= 32
  x13 <<= 32
  x12 += x13


  (uint32) x0 += j0
  x1 <<= 32
  x1 += j0
  (uint64) x1 >>= 32
  x1 <<= 32
  x0 += x1

  (uint32) x4 += j4
  x5 <<= 32
  x5 += j4
  (uint64) x5 >>= 32
  x5 <<= 32
  x4 += x5

  x11 = x11_stack

  (uint32) x10 += j10
  x11 <<= 32
  x11 += j10
  (uint64) x11 >>= 32
  x11 <<= 32
  x10 += x11

  (uint32) x14 += j14
  x15 <<= 32
  x15 += j14
  (uint64) x15 >>= 32
  x15 <<= 32
  x14 += x15

  out = out_backup
  m = m_backup

  x0 ^= *(uint64 *) (m + 0)
  *(uint64 *) (out + 0) = x0

  x2 ^= *(uint64 *) (m + 8)
  *(uint64 *) (out + 8) = x2

  x4 ^= *(uint64 *) (m + 16)
  *(uint64 *) (out + 16) = x4

  x6 ^= *(uint64 *) (m + 24)
  *(uint64 *) (out + 24) = x6

  x8 ^= *(uint64 *) (m + 32)
  *(uint64 *) (out + 32) = x8

  x10 ^= *(uint64 *) (m + 40)
  *(uint64 *) (out + 40) = x10

  x12 ^= *(uint64 *) (m + 48)
  *(uint64 *) (out + 48) = x12

  x14 ^= *(uint64 *) (m + 56)
  *(uint64 *) (out + 56) = x14


  bytes = bytes_backup

  in12 = j12
  in12 += 1
  j12 = in12

                         unsigned>? unsigned<? bytes - 64
  goto bytesatleast65 if unsigned>

    goto bytesatleast64 if !unsigned<
      m = out
      out = ctarget
      i = bytes
      while (i) { *out++ = *m++; --i }
    bytesatleast64:

    x = x_backup
    in12 = j12
    *(uint64 *) (x + 48) = in12

    r11 = r11_stack
    r12 = r12_stack
    r13 = r13_stack
    r14 = r14_stack
    r15 = r15_stack
    rbx = rbx_stack
    rbp = rbp_stack

    done:

    leave

  bytesatleast65:

  bytes -= 64
  out += 64
  m += 64
goto bytesatleast1


enter ECRYPT_init
leave


enter ECRYPT_keysetup

  k = arg2
  kbits = arg3
  x = arg1

  in4 = *(uint64 *) (k + 0)
  in6 = *(uint64 *) (k + 8)
  *(uint64 *) (x + 16) = in4
  *(uint64 *) (x + 24) = in6

                   unsigned<? kbits - 256
  goto kbits128 if unsigned<

  kbits256:

    in8 = *(uint64 *) (k + 16)
    in10 = *(uint64 *) (k + 24)
    *(uint64 *) (x + 32) = in8
    *(uint64 *) (x + 40) = in10

    in0 = 1634760805
    in1 = 857760878
    in2 = 2036477234
    in3 = 1797285236
    *(uint32 *) (x + 0) = in0
    *(uint32 *) (x + 4) = in1
    *(uint32 *) (x + 8) = in2
    *(uint32 *) (x + 12) = in3

  goto keysetupdone

  kbits128:

    in8 = *(uint64 *) (k + 0)
    in10 = *(uint64 *) (k + 8)
    *(uint64 *) (x + 32) = in8
    *(uint64 *) (x + 40) = in10

    in0 = 1634760805
    in1 = 824206446
    in2 = 2036477238
    in3 = 1797285236
    *(uint32 *) (x + 0) = in0
    *(uint32 *) (x + 4) = in1
    *(uint32 *) (x + 8) = in2
    *(uint32 *) (x + 12) = in3

  keysetupdone:

leave


enter ECRYPT_ivsetup

  iv = arg2
  x = arg1

  in12 = 0
  in14 = *(uint64 *) (iv + 0)
  *(uint64 *) (x + 48) = in12
  *(uint64 *) (x + 56) = in14

leave
