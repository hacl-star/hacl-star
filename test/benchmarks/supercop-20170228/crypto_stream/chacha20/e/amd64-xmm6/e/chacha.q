# 20080118
# D. J. Bernstein
# Public domain.

int64 a

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

int64 i

int64 x
int64 m
int64 out
int64 bytes

int6464 diag0
int6464 diag1
int6464 diag2
int6464 diag3

int6464 a0
int6464 a1
int6464 a2
int6464 a3
int6464 a4
int6464 a5
int6464 a6
int6464 a7
int6464 b0
int6464 b1
int6464 b2
int6464 b3
int6464 b4
int6464 b5
int6464 b6
int6464 b7

int6464 z0
int6464 z1
int6464 z2
int6464 z3
int6464 z4
int6464 z5
int6464 z6
int6464 z7
int6464 z8
int6464 z9
int6464 z10
int6464 z11
int6464 z12
int6464 z13
int6464 z14
int6464 z15

stack128 z0_stack
stack128 z1_stack
stack128 z2_stack
stack128 z3_stack
stack128 z4_stack
stack128 z5_stack
stack128 z6_stack
stack128 z7_stack
stack128 z8_stack
stack128 z9_stack
stack128 z10_stack
stack128 z11_stack
stack128 z12_stack
stack128 z13_stack
stack128 z14_stack
stack128 z15_stack

int6464 y0
int6464 y1
int6464 y2
int6464 y3
int6464 y4
int6464 y5
int6464 y6
int6464 y7
int6464 y8
int6464 y9
int6464 y10
int6464 y11
int6464 y12
int6464 y13
int6464 y14
int6464 y15

int6464 shift4
int6464 shift5
int6464 shift6
int6464 shift7
int6464 shift12
int6464 shift13
int6464 shift14
int6464 shift15

stack128 orig0
stack128 orig1
stack128 orig2
stack128 orig3
stack128 orig4
stack128 orig5
stack128 orig6
stack128 orig7
stack128 orig8
stack128 orig9
stack128 orig10
stack128 orig11
stack128 orig12
stack128 orig13
stack128 orig14
stack128 orig15

int64 in0
int64 in1
int64 in2
int64 in3
int64 in4
int64 in5
int64 in6
int64 in7
int64 in8
int64 in9
int64 in10
int64 in11
int64 in12
int64 in13
int64 in14
int64 in15

stack512 tmp

int64 ctarget
stack64 bytes_backup


enter ECRYPT_keystream_bytes

x = arg1
m = arg2
out = m
bytes = arg3

              unsigned>? bytes - 0
goto done if !unsigned>

a = 0
i = bytes
while (i) { *out++ = a; --i }
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

                              unsigned<? bytes - 256
  goto bytesbetween1and255 if unsigned<

  z0 = *(int128 *) (x + 0)
  z1 = z0[1,1,1,1]
  z2 = z0[2,2,2,2]
  z3 = z0[3,3,3,3]
  z0 = z0[0,0,0,0]
  orig0 = z0
  orig1 = z1
  orig2 = z2
  orig3 = z3

  z4 = *(int128 *) (x + 16)
  z5 = z4[1,1,1,1]
  z6 = z4[2,2,2,2]
  z7 = z4[3,3,3,3]
  z4 = z4[0,0,0,0]
  orig4 = z4
  orig5 = z5
  orig6 = z6
  orig7 = z7

  z8 = *(int128 *) (x + 32)
  z9 = z8[1,1,1,1]
  z10 = z8[2,2,2,2]
  z11 = z8[3,3,3,3]
  z8 = z8[0,0,0,0]
  orig8 = z8
  orig9 = z9
  orig10 = z10
  orig11 = z11

  z12 = *(int128 *) (x + 48)
  z14 = z12[2,2,2,2]
  z15 = z12[3,3,3,3]
  orig14 = z14
  orig15 = z15

bytesatleast256:

  bytes_backup = bytes

  in0 = *(uint64 *) (x + 48)
  in1 = in0 + 1
  in2 = in0 + 2
  in3 = in0 + 3
  in4 = in0 + 4

  ((uint32 *) &orig12)[0] = in0
  ((uint32 *) &orig12)[1] = in1
  ((uint32 *) &orig12)[2] = in2
  ((uint32 *) &orig12)[3] = in3

  (uint64) in0 >>= 32
  (uint64) in1 >>= 32
  (uint64) in2 >>= 32
  (uint64) in3 >>= 32

  ((uint32 *) &orig13)[0] = in0
  ((uint32 *) &orig13)[1] = in1
  ((uint32 *) &orig13)[2] = in2
  ((uint32 *) &orig13)[3] = in3

  *(uint64 *) (x + 48) = in4

i = 20

  z2 = orig2
  z6 = orig6
  z10 = orig10
  z14 = orig14

  z3 = orig3
  z7 = orig7
  z11 = orig11
  z15 = orig15

  z0 = orig0
  z4 = orig4
  z8 = orig8
  z12 = orig12

  z1 = orig1
  z5 = orig5
  z9 = orig9
  z13 = orig13

								z11_stack = z11

mainloop1:

uint32323232	z0 += z4
		z12 ^= z0
uint32323232			z1 += z5
				z13 ^= z1
		shift12 = z12
uint32323232	z12 >>= 16
uint32323232	shift12 <<= 16
		z12 ^= shift12

				shift13 = z13
uint32323232			z13 >>= 16
uint32323232			shift13 <<= 16
				z13 ^= shift13

uint32323232	z8 += z12
		z4 ^= z8
uint32323232			z9 += z13
				z5 ^= z9
		shift4 = z4
uint32323232	z4 >>= 20
uint32323232	shift4 <<= 12
		z4 ^= shift4

				shift5 = z5
uint32323232			z5 >>= 20
uint32323232			shift5 <<= 12
				z5 ^= shift5

uint32323232	z0 += z4
		z12 ^= z0
		shift12 = z12
uint32323232	z12 >>= 24
uint32323232	shift12 <<= 8
		z12 ^= shift12

uint32323232			z1 += z5
				z13 ^= z1
				shift13 = z13
uint32323232			z13 >>= 24
uint32323232			shift13 <<= 8
				z13 ^= shift13

uint32323232	z8 += z12
		z4 ^= z8
		shift4 = z4
uint32323232	z4 >>= 25
uint32323232	shift4 <<= 7
		z4 ^= shift4

uint32323232			z9 += z13
				z5 ^= z9
				shift5 = z5
uint32323232			z5 >>= 25
uint32323232			shift5 <<= 7
				z5 ^= shift5

				z9_stack = z9
								z11 = z11_stack

uint32323232					z2 += z6
						z14 ^= z2
						shift14 = z14
uint32323232					z14 >>= 16
uint32323232					shift14 <<= 16
						z14 ^= shift14

uint32323232							z3 += z7
								z15 ^= z3
								shift15 = z15
uint32323232							z15 >>= 16
uint32323232							shift15 <<= 16
								z15 ^= shift15

uint32323232					z10 += z14
						z6 ^= z10
						shift6 = z6
uint32323232					z6 >>= 20
uint32323232					shift6 <<= 12
						z6 ^= shift6

uint32323232							z11 += z15
								z7 ^= z11
								shift7 = z7
uint32323232							z7 >>= 20
uint32323232							shift7 <<= 12
								z7 ^= shift7

uint32323232					z2 += z6
						z14 ^= z2
						shift14 = z14
uint32323232					z14 >>= 24
uint32323232					shift14 <<= 8
						z14 ^= shift14

uint32323232							z3 += z7
								z15 ^= z3
								shift15 = z15
uint32323232							z15 >>= 24
uint32323232							shift15 <<= 8
								z15 ^= shift15

uint32323232					z10 += z14
						z6 ^= z10
						shift6 = z6
uint32323232					z6 >>= 25
uint32323232					shift6 <<= 7
						z6 ^= shift6

uint32323232							z11 += z15
								z7 ^= z11
								shift7 = z7
uint32323232							z7 >>= 25
uint32323232							shift7 <<= 7
								z7 ^= shift7

uint32323232	z0 += z5
		z15 ^= z0
		shift15 = z15
uint32323232	z15 >>= 16
uint32323232	shift15 <<= 16
		z15 ^= shift15

uint32323232			z1 += z6
				z12 ^= z1
				shift13 = z12
uint32323232			z12 >>= 16
uint32323232			shift13 <<= 16
				z12 ^= shift13

uint32323232	z10 += z15
		z5 ^= z10
		shift5 = z5
uint32323232	z5 >>= 20
uint32323232	shift5 <<= 12
		z5 ^= shift5

uint32323232			z11 += z12
				z6 ^= z11
				shift6 = z6
uint32323232			z6 >>= 20
uint32323232			shift6 <<= 12
				z6 ^= shift6

uint32323232	z0 += z5
		z15 ^= z0
		shift15 = z15
uint32323232	z15 >>= 24
uint32323232	shift15 <<= 8
		z15 ^= shift15

uint32323232			z1 += z6
				z12 ^= z1
				shift13 = z12
uint32323232			z12 >>= 24
uint32323232			shift13 <<= 8
				z12 ^= shift13

uint32323232	z10 += z15
		z5 ^= z10
		shift5 = z5
uint32323232	z5 >>= 25
uint32323232	shift5 <<= 7
		z5 ^= shift5

uint32323232			z11 += z12
				z6 ^= z11
				shift6 = z6
uint32323232			z6 >>= 25
uint32323232			shift6 <<= 7
				z6 ^= shift6

				z11_stack = z11
								z9 = z9_stack

uint32323232					z2 += z7
						z13 ^= z2
						shift13 = z13
uint32323232					z13 >>= 16
uint32323232					shift13 <<= 16
						z13 ^= shift13

uint32323232							z3 += z4
								z14 ^= z3
								shift14 = z14
uint32323232							z14 >>= 16
uint32323232							shift14 <<= 16
								z14 ^= shift14

uint32323232					z8 += z13
						z7 ^= z8
						shift7 = z7
uint32323232					z7 >>= 20
uint32323232					shift7 <<= 12
						z7 ^= shift7

                  unsigned>? i -= 2

uint32323232							z9 += z14
								z4 ^= z9
								shift4 = z4
uint32323232							z4 >>= 20
uint32323232							shift4 <<= 12
								z4 ^= shift4

uint32323232					z2 += z7
						z13 ^= z2
						shift13 = z13
uint32323232					z13 >>= 24
uint32323232					shift13 <<= 8
						z13 ^= shift13

uint32323232							z3 += z4
								z14 ^= z3
								shift14 = z14
uint32323232							z14 >>= 24
uint32323232							shift14 <<= 8
								z14 ^= shift14

uint32323232					z8 += z13
						z7 ^= z8
						shift7 = z7
uint32323232					z7 >>= 25
uint32323232					shift7 <<= 7
						z7 ^= shift7

uint32323232							z9 += z14
								z4 ^= z9
								shift4 = z4
uint32323232							z4 >>= 25
uint32323232							shift4 <<= 7
								z4 ^= shift4


goto mainloop1 if unsigned>

								z11 = z11_stack

  uint32323232 z0 += orig0
  uint32323232 z1 += orig1
  uint32323232 z2 += orig2
  uint32323232 z3 += orig3
  in0 = z0
  in1 = z1
  in2 = z2
  in3 = z3
  z0 <<<= 96
  z1 <<<= 96
  z2 <<<= 96
  z3 <<<= 96
  (uint32) in0 ^= *(uint32 *) (m + 0)
  (uint32) in1 ^= *(uint32 *) (m + 4)
  (uint32) in2 ^= *(uint32 *) (m + 8)
  (uint32) in3 ^= *(uint32 *) (m + 12)
  *(uint32 *) (out + 0) = in0
  *(uint32 *) (out + 4) = in1
  *(uint32 *) (out + 8) = in2
  *(uint32 *) (out + 12) = in3
  in0 = z0
  in1 = z1
  in2 = z2
  in3 = z3
  z0 <<<= 96
  z1 <<<= 96
  z2 <<<= 96
  z3 <<<= 96
  (uint32) in0 ^= *(uint32 *) (m + 64)
  (uint32) in1 ^= *(uint32 *) (m + 68)
  (uint32) in2 ^= *(uint32 *) (m + 72)
  (uint32) in3 ^= *(uint32 *) (m + 76)
  *(uint32 *) (out + 64) = in0
  *(uint32 *) (out + 68) = in1
  *(uint32 *) (out + 72) = in2
  *(uint32 *) (out + 76) = in3
  in0 = z0
  in1 = z1
  in2 = z2
  in3 = z3
  z0 <<<= 96
  z1 <<<= 96
  z2 <<<= 96
  z3 <<<= 96
  (uint32) in0 ^= *(uint32 *) (m + 128)
  (uint32) in1 ^= *(uint32 *) (m + 132)
  (uint32) in2 ^= *(uint32 *) (m + 136)
  (uint32) in3 ^= *(uint32 *) (m + 140)
  *(uint32 *) (out + 128) = in0
  *(uint32 *) (out + 132) = in1
  *(uint32 *) (out + 136) = in2
  *(uint32 *) (out + 140) = in3
  in0 = z0
  in1 = z1
  in2 = z2
  in3 = z3
  (uint32) in0 ^= *(uint32 *) (m + 192)
  (uint32) in1 ^= *(uint32 *) (m + 196)
  (uint32) in2 ^= *(uint32 *) (m + 200)
  (uint32) in3 ^= *(uint32 *) (m + 204)
  *(uint32 *) (out + 192) = in0
  *(uint32 *) (out + 196) = in1
  *(uint32 *) (out + 200) = in2
  *(uint32 *) (out + 204) = in3

  uint32323232 z4 += orig4
  uint32323232 z5 += orig5
  uint32323232 z6 += orig6
  uint32323232 z7 += orig7
  in4 = z4
  in5 = z5
  in6 = z6
  in7 = z7
  z4 <<<= 96
  z5 <<<= 96
  z6 <<<= 96
  z7 <<<= 96
  (uint32) in4 ^= *(uint32 *) (m + 16)
  (uint32) in5 ^= *(uint32 *) (m + 20)
  (uint32) in6 ^= *(uint32 *) (m + 24)
  (uint32) in7 ^= *(uint32 *) (m + 28)
  *(uint32 *) (out + 16) = in4
  *(uint32 *) (out + 20) = in5
  *(uint32 *) (out + 24) = in6
  *(uint32 *) (out + 28) = in7
  in4 = z4
  in5 = z5
  in6 = z6
  in7 = z7
  z4 <<<= 96
  z5 <<<= 96
  z6 <<<= 96
  z7 <<<= 96
  (uint32) in4 ^= *(uint32 *) (m + 80)
  (uint32) in5 ^= *(uint32 *) (m + 84)
  (uint32) in6 ^= *(uint32 *) (m + 88)
  (uint32) in7 ^= *(uint32 *) (m + 92)
  *(uint32 *) (out + 80) = in4
  *(uint32 *) (out + 84) = in5
  *(uint32 *) (out + 88) = in6
  *(uint32 *) (out + 92) = in7
  in4 = z4
  in5 = z5
  in6 = z6
  in7 = z7
  z4 <<<= 96
  z5 <<<= 96
  z6 <<<= 96
  z7 <<<= 96
  (uint32) in4 ^= *(uint32 *) (m + 144)
  (uint32) in5 ^= *(uint32 *) (m + 148)
  (uint32) in6 ^= *(uint32 *) (m + 152)
  (uint32) in7 ^= *(uint32 *) (m + 156)
  *(uint32 *) (out + 144) = in4
  *(uint32 *) (out + 148) = in5
  *(uint32 *) (out + 152) = in6
  *(uint32 *) (out + 156) = in7
  in4 = z4
  in5 = z5
  in6 = z6
  in7 = z7
  (uint32) in4 ^= *(uint32 *) (m + 208)
  (uint32) in5 ^= *(uint32 *) (m + 212)
  (uint32) in6 ^= *(uint32 *) (m + 216)
  (uint32) in7 ^= *(uint32 *) (m + 220)
  *(uint32 *) (out + 208) = in4
  *(uint32 *) (out + 212) = in5
  *(uint32 *) (out + 216) = in6
  *(uint32 *) (out + 220) = in7

  uint32323232 z8 += orig8
  uint32323232 z9 += orig9
  uint32323232 z10 += orig10
  uint32323232 z11 += orig11
  in8 = z8
  in9 = z9
  in10 = z10
  in11 = z11
  z8 <<<= 96
  z9 <<<= 96
  z10 <<<= 96
  z11 <<<= 96
  (uint32) in8 ^= *(uint32 *) (m + 32)
  (uint32) in9 ^= *(uint32 *) (m + 36)
  (uint32) in10 ^= *(uint32 *) (m + 40)
  (uint32) in11 ^= *(uint32 *) (m + 44)
  *(uint32 *) (out + 32) = in8
  *(uint32 *) (out + 36) = in9
  *(uint32 *) (out + 40) = in10
  *(uint32 *) (out + 44) = in11
  in8 = z8
  in9 = z9
  in10 = z10
  in11 = z11
  z8 <<<= 96
  z9 <<<= 96
  z10 <<<= 96
  z11 <<<= 96
  (uint32) in8 ^= *(uint32 *) (m + 96)
  (uint32) in9 ^= *(uint32 *) (m + 100)
  (uint32) in10 ^= *(uint32 *) (m + 104)
  (uint32) in11 ^= *(uint32 *) (m + 108)
  *(uint32 *) (out + 96) = in8
  *(uint32 *) (out + 100) = in9
  *(uint32 *) (out + 104) = in10
  *(uint32 *) (out + 108) = in11
  in8 = z8
  in9 = z9
  in10 = z10
  in11 = z11
  z8 <<<= 96
  z9 <<<= 96
  z10 <<<= 96
  z11 <<<= 96
  (uint32) in8 ^= *(uint32 *) (m + 160)
  (uint32) in9 ^= *(uint32 *) (m + 164)
  (uint32) in10 ^= *(uint32 *) (m + 168)
  (uint32) in11 ^= *(uint32 *) (m + 172)
  *(uint32 *) (out + 160) = in8
  *(uint32 *) (out + 164) = in9
  *(uint32 *) (out + 168) = in10
  *(uint32 *) (out + 172) = in11
  in8 = z8
  in9 = z9
  in10 = z10
  in11 = z11
  (uint32) in8 ^= *(uint32 *) (m + 224)
  (uint32) in9 ^= *(uint32 *) (m + 228)
  (uint32) in10 ^= *(uint32 *) (m + 232)
  (uint32) in11 ^= *(uint32 *) (m + 236)
  *(uint32 *) (out + 224) = in8
  *(uint32 *) (out + 228) = in9
  *(uint32 *) (out + 232) = in10
  *(uint32 *) (out + 236) = in11

  uint32323232 z12 += orig12
  uint32323232 z13 += orig13
  uint32323232 z14 += orig14
  uint32323232 z15 += orig15
  in12 = z12
  in13 = z13
  in14 = z14
  in15 = z15
  z12 <<<= 96
  z13 <<<= 96
  z14 <<<= 96
  z15 <<<= 96
  (uint32) in12 ^= *(uint32 *) (m + 48)
  (uint32) in13 ^= *(uint32 *) (m + 52)
  (uint32) in14 ^= *(uint32 *) (m + 56)
  (uint32) in15 ^= *(uint32 *) (m + 60)
  *(uint32 *) (out + 48) = in12
  *(uint32 *) (out + 52) = in13
  *(uint32 *) (out + 56) = in14
  *(uint32 *) (out + 60) = in15
  in12 = z12
  in13 = z13
  in14 = z14
  in15 = z15
  z12 <<<= 96
  z13 <<<= 96
  z14 <<<= 96
  z15 <<<= 96
  (uint32) in12 ^= *(uint32 *) (m + 112)
  (uint32) in13 ^= *(uint32 *) (m + 116)
  (uint32) in14 ^= *(uint32 *) (m + 120)
  (uint32) in15 ^= *(uint32 *) (m + 124)
  *(uint32 *) (out + 112) = in12
  *(uint32 *) (out + 116) = in13
  *(uint32 *) (out + 120) = in14
  *(uint32 *) (out + 124) = in15
  in12 = z12
  in13 = z13
  in14 = z14
  in15 = z15
  z12 <<<= 96
  z13 <<<= 96
  z14 <<<= 96
  z15 <<<= 96
  (uint32) in12 ^= *(uint32 *) (m + 176)
  (uint32) in13 ^= *(uint32 *) (m + 180)
  (uint32) in14 ^= *(uint32 *) (m + 184)
  (uint32) in15 ^= *(uint32 *) (m + 188)
  *(uint32 *) (out + 176) = in12
  *(uint32 *) (out + 180) = in13
  *(uint32 *) (out + 184) = in14
  *(uint32 *) (out + 188) = in15
  in12 = z12
  in13 = z13
  in14 = z14
  in15 = z15
  (uint32) in12 ^= *(uint32 *) (m + 240)
  (uint32) in13 ^= *(uint32 *) (m + 244)
  (uint32) in14 ^= *(uint32 *) (m + 248)
  (uint32) in15 ^= *(uint32 *) (m + 252)
  *(uint32 *) (out + 240) = in12
  *(uint32 *) (out + 244) = in13
  *(uint32 *) (out + 248) = in14
  *(uint32 *) (out + 252) = in15

  bytes = bytes_backup

  bytes -= 256
  m += 256
  out += 256
                           unsigned<? bytes - 256
  goto bytesatleast256 if !unsigned<

                unsigned>? bytes - 0
  goto done if !unsigned>

bytesbetween1and255:

                  unsigned<? bytes - 64
  goto nocopy if !unsigned<

    ctarget = out

    out = &tmp
    i = bytes
    while (i) { *out++ = *m++; --i }
    out = &tmp
    m = &tmp

  nocopy:

  bytes_backup = bytes



diag0 = *(int128 *) (x + 0)
diag1 = *(int128 *) (x + 16)
diag2 = *(int128 *) (x + 32)
diag3 = *(int128 *) (x + 48)

i = 20

mainloop2:

uint32323232    diag0 += diag1
                diag3 ^= diag0
                b3 = diag3
uint32323232    diag3 <<= 16
uint32323232    b3 >>= 16
                diag3 ^= b3

uint32323232                    diag2 += diag3
                                diag1 ^= diag2
                                b1 = diag1
uint32323232                    diag1 <<= 12
uint32323232                    b1 >>= 20
                                diag1 ^= b1

uint32323232                                    diag0 += diag1
                                                diag3 ^= diag0
                                                b3 = diag3
uint32323232                                    diag3 <<= 8
uint32323232                                    b3 >>= 24
                diag0 <<<= 32
                                                diag3 ^= b3

uint32323232                                                    diag2 += diag3
                diag3 <<<= 64
                                                                diag1 ^= diag2
                diag2 <<<= 96
                                                                b1 = diag1
uint32323232                                                    diag1 <<= 7
uint32323232                                                    b1 >>= 25
                                                                diag1 ^= b1

                 unsigned>? i -= 2

uint32323232    diag0 += diag1
                diag3 ^= diag0
                b3 = diag3
uint32323232    diag3 <<= 16
uint32323232    b3 >>= 16
                diag3 ^= b3

uint32323232                    diag2 += diag3
                                diag1 ^= diag2
                                b1 = diag1
uint32323232                    diag1 <<= 12
uint32323232                    b1 >>= 20
                                diag1 ^= b1

uint32323232                                    diag0 += diag1
                                                diag3 ^= diag0
                                                b3 = diag3
uint32323232                                    diag3 <<= 8
uint32323232                                    b3 >>= 24
                diag0 <<<= 96
                                                diag3 ^= b3

uint32323232                                                    diag2 += diag3
                diag3 <<<= 64
                                                                diag1 ^= diag2
                diag2 <<<= 32
                                                                b1 = diag1
uint32323232                                                    diag1 <<= 7
uint32323232                                                    b1 >>= 25
                                                                diag1 ^= b1

goto mainloop2 if unsigned>


uint32323232 diag0 += *(int128 *) (x + 0)
uint32323232 diag1 += *(int128 *) (x + 16)
uint32323232 diag2 += *(int128 *) (x + 32)
uint32323232 diag3 += *(int128 *) (x + 48)

uint32323232 diag0 ^= *(int128 *) (m + 0)
uint32323232 diag1 ^= *(int128 *) (m + 16)
uint32323232 diag2 ^= *(int128 *) (m + 32)
uint32323232 diag3 ^= *(int128 *) (m + 48)

*(int128 *) (out + 0) = diag0
*(int128 *) (out + 16) = diag1
*(int128 *) (out + 32) = diag2
*(int128 *) (out + 48) = diag3


  bytes = bytes_backup

  in12 = *(uint32 *) (x + 48)
  in13 = *(uint32 *) (x + 52)
  in12 += 1
  in13 <<= 32
  in12 += in13
  in13 = in12
  (uint64) in13 >>= 32
  *(uint32 *) (x + 48) = in12
  *(uint32 *) (x + 52) = in13

                         unsigned>? unsigned<? bytes - 64
  goto bytesatleast65 if unsigned>

    goto bytesatleast64 if !unsigned<
      m = out
      out = ctarget
      i = bytes
      while (i) { *out++ = *m++; --i }
    bytesatleast64:
    done:

    leave

  bytesatleast65:

  bytes -= 64
  out += 64
  m += 64
goto bytesbetween1and255


enter ECRYPT_init
leave


enter ECRYPT_keysetup

  k = arg2
  kbits = arg3
  x = arg1

  in4 = *(uint32 *) (k + 0)
  in5 = *(uint32 *) (k + 4)
  in6 = *(uint32 *) (k + 8)
  in7 = *(uint32 *) (k + 12)
  *(uint32 *) (x + 16) = in4
  *(uint32 *) (x + 20) = in5
  *(uint32 *) (x + 24) = in6
  *(uint32 *) (x + 28) = in7

                   unsigned<? kbits - 256
  goto kbits128 if unsigned<

  kbits256:

    in8 = *(uint32 *) (k + 16)
    in9 = *(uint32 *) (k + 20)
    in10 = *(uint32 *) (k + 24)
    in11 = *(uint32 *) (k + 28)
    *(uint32 *) (x + 32) = in8
    *(uint32 *) (x + 36) = in9
    *(uint32 *) (x + 40) = in10
    *(uint32 *) (x + 44) = in11

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

    in8 = *(uint32 *) (k + 0)
    in9 = *(uint32 *) (k + 4)
    in10 = *(uint32 *) (k + 8)
    in11 = *(uint32 *) (k + 12)
    *(uint32 *) (x + 32) = in8
    *(uint32 *) (x + 36) = in9
    *(uint32 *) (x + 40) = in10
    *(uint32 *) (x + 44) = in11

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
  in13 = 0
  in14 = *(uint32 *) (iv + 0)
  in15 = *(uint32 *) (iv + 4)
  *(uint32 *) (x + 48) = in12
  *(uint32 *) (x + 52) = in13
  *(uint32 *) (x + 56) = in14
  *(uint32 *) (x + 60) = in15

leave
