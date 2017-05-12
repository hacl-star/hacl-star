enter crypto_core_salsa20_armneon2

int32 i

int128 abab
int128 k0k1k2k3
int128 k4k5k6k7
int128 n0n1n2n3
int128 n1n2n3n0
int128 k4k5k0n0
int128 n1n2k6k1
int128 k2k3n3k7
int128 start0
int128 start1
int128 start2
int128 start3
int128 diag0
int128 diag1
int128 diag2
int128 diag3
int128 x0x5x10x15
int128 x12x1x6x11
int128 x8x13x2x7
int128 x4x9x14x3
int128 x0x1x10x11
int128 x12x13x6x7
int128 x8x9x2x3
int128 x4x5x14x15
int128 x0x1x2x3
int128 x4x5x6x7
int128 x8x9x10x11
int128 x12x13x14x15
int128 a0
int128 a1
int128 a2
int128 a3
int128 b0
int128 b1
int128 b2
int128 b3

n0n1n2n3 = mem128[input_1]
n1n2n3n0 = n0n1n2n3[1,2,3] n0n1n2n3[0]

k0k1k2k3 = mem128[input_2]
input_2 += 16
k4k5k6k7 = mem128[input_2]

n1n2k6k1 = n1n2n3n0
k2k3n3k7 = k0k1k2k3[2,3] k0k1k2k3[0,1]
k4k5k0n0 = k4k5k6k7

n1n2k6k1 = n1n2k6k1[0,1] k0k1k2k3[1] k4k5k6k7[2]
k2k3n3k7 = k2k3n3k7[0,1] k4k5k6k7[3] n1n2n3n0[2]
k4k5k0n0 = k4k5k0n0[0,1] n1n2n3n0[3] k0k1k2k3[0]

n1n2k6k1 = n1n2k6k1[0,1] n1n2k6k1[3] n1n2k6k1[2]
k2k3n3k7 = k2k3n3k7[0,1] k2k3n3k7[3] k2k3n3k7[2]
k4k5k0n0 = k4k5k0n0[0,1] k4k5k0n0[3] k4k5k0n0[2]

diag0 = mem128[input_3]
diag2 = n1n2k6k1[1,2,3] n1n2k6k1[0]
diag3 = k2k3n3k7[1,2,3] k2k3n3k7[0]
diag1 = k4k5k0n0[1,2,3] k4k5k0n0[0]

start0 = diag0
start1 = diag1
start2 = diag2
start3 = diag3

i = 20

mainloop:

  4x a0 = diag1 + diag0
  4x b0 = a0 << 7
  4x b0 insert= a0 >> 25
     diag3 ^= b0
  4x a1 = diag0 + diag3
  4x b1 = a1 << 9
  4x b1 insert= a1 >> 23
     diag2 ^= b1
  4x a2 = diag3 + diag2
          diag3 = diag3[3] diag3[0,1,2]
  4x b2 = a2 << 13
  4x b2 insert= a2 >> 19
     diag1 ^= b2
  4x a3 = diag2 + diag1
          diag2 = diag2[2,3] diag2[0,1]
  4x b3 = a3 << 18
  4x b3 insert= a3 >> 14
          diag1 = diag1[1,2,3] diag1[0]
     diag0 ^= b3

                 unsigned>? i -= 2

  4x a0 = diag3 + diag0
  4x b0 = a0 << 7
  4x b0 insert= a0 >> 25
     diag1 ^= b0
  4x a1 = diag0 + diag1
  4x b1 = a1 << 9
  4x b1 insert= a1 >> 23
     diag2 ^= b1
  4x a2 = diag1 + diag2
          diag1 = diag1[3] diag1[0,1,2]
  4x b2 = a2 << 13
  4x b2 insert= a2 >> 19
     diag3 ^= b2
  4x a3 = diag2 + diag3
          diag2 = diag2[2,3] diag2[0,1]
  4x b3 = a3 << 18
  4x b3 insert= a3 >> 14
          diag3 = diag3[1,2,3] diag3[0]
     diag0 ^= b3

goto mainloop if unsigned>

2x abab = 0xffffffff

4x x0x5x10x15 = diag0 + start0
4x x12x1x6x11 = diag1 + start1
4x x8x13x2x7 = diag2 + start2
4x x4x9x14x3 = diag3 + start3

x0x1x10x11 = x0x5x10x15
x12x13x6x7 = x12x1x6x11
x8x9x2x3 = x8x13x2x7
x4x5x14x15 = x4x9x14x3

x0x1x10x11 = (abab & x0x1x10x11) | (~abab & x12x1x6x11)
x12x13x6x7 = (abab & x12x13x6x7) | (~abab & x8x13x2x7)
x8x9x2x3 = (abab & x8x9x2x3) | (~abab & x4x9x14x3)
x4x5x14x15 = (abab & x4x5x14x15) | (~abab & x0x5x10x15)

x0x1x2x3 = x0x1x10x11
x4x5x6x7 = x4x5x14x15
x8x9x10x11 = x8x9x2x3
x12x13x14x15 = x12x13x6x7

x0x1x2x3 = x0x1x2x3[0,1] x8x9x2x3[2,3]
x4x5x6x7 = x4x5x6x7[0,1] x12x13x6x7[2,3]
x8x9x10x11 = x8x9x10x11[0,1] x0x1x10x11[2,3]
x12x13x14x15 = x12x13x14x15[0,1] x4x5x14x15[2,3]

mem128[input_0] = x0x1x2x3
input_0 += 16
mem128[input_0] = x4x5x6x7
input_0 += 16
mem128[input_0] = x8x9x10x11
input_0 += 16
mem128[input_0] = x12x13x14x15

int32 result
result = 0

return result
