
# qhasm: int32 input_0

# qhasm: int32 input_1

# qhasm: int32 input_2

# qhasm: int32 input_3

# qhasm: stack32 input_4

# qhasm: stack32 input_5

# qhasm: stack32 input_6

# qhasm: stack32 input_7

# qhasm: int32 caller_r4

# qhasm: int32 caller_r5

# qhasm: int32 caller_r6

# qhasm: int32 caller_r7

# qhasm: int32 caller_r8

# qhasm: int32 caller_r9

# qhasm: int32 caller_r10

# qhasm: int32 caller_r11

# qhasm: int32 caller_r14

# qhasm: reg128 caller_q4

# qhasm: reg128 caller_q5

# qhasm: reg128 caller_q6

# qhasm: reg128 caller_q7

# qhasm: startcode
.fpu neon
.text

# qhasm: enter crypto_core_salsa20_armneon2
.align 2
.global _crypto_core_salsa20_armneon2
.global crypto_core_salsa20_armneon2
.type _crypto_core_salsa20_armneon2 STT_FUNC
.type crypto_core_salsa20_armneon2 STT_FUNC
_crypto_core_salsa20_armneon2:
crypto_core_salsa20_armneon2:
sub sp,sp,#0

# qhasm: int32 i

# qhasm: int128 abab

# qhasm: int128 k0k1k2k3

# qhasm: int128 k4k5k6k7

# qhasm: int128 n0n1n2n3

# qhasm: int128 n1n2n3n0

# qhasm: int128 k4k5k0n0

# qhasm: int128 n1n2k6k1

# qhasm: int128 k2k3n3k7

# qhasm: int128 start0

# qhasm: int128 start1

# qhasm: int128 start2

# qhasm: int128 start3

# qhasm: int128 diag0

# qhasm: int128 diag1

# qhasm: int128 diag2

# qhasm: int128 diag3

# qhasm: int128 x0x5x10x15

# qhasm: int128 x12x1x6x11

# qhasm: int128 x8x13x2x7

# qhasm: int128 x4x9x14x3

# qhasm: int128 x0x1x10x11

# qhasm: int128 x12x13x6x7

# qhasm: int128 x8x9x2x3

# qhasm: int128 x4x5x14x15

# qhasm: int128 x0x1x2x3

# qhasm: int128 x4x5x6x7

# qhasm: int128 x8x9x10x11

# qhasm: int128 x12x13x14x15

# qhasm: int128 a0

# qhasm: int128 a1

# qhasm: int128 a2

# qhasm: int128 a3

# qhasm: int128 b0

# qhasm: int128 b1

# qhasm: int128 b2

# qhasm: int128 b3

# qhasm: n0n1n2n3 = mem128[input_1]
# asm 1: vld1.8 {>n0n1n2n3=reg128#1%bot->n0n1n2n3=reg128#1%top},[<input_1=int32#2]
# asm 2: vld1.8 {>n0n1n2n3=d0->n0n1n2n3=d1},[<input_1=r1]
vld1.8 {d0-d1},[r1]

# qhasm: n1n2n3n0 = n0n1n2n3[1,2,3] n0n1n2n3[0]
# asm 1: vext.32 >n1n2n3n0=reg128#1,<n0n1n2n3=reg128#1,<n0n1n2n3=reg128#1,#1
# asm 2: vext.32 >n1n2n3n0=q0,<n0n1n2n3=q0,<n0n1n2n3=q0,#1
vext.32 q0,q0,q0,#1

# qhasm: k0k1k2k3 = mem128[input_2]
# asm 1: vld1.8 {>k0k1k2k3=reg128#2%bot->k0k1k2k3=reg128#2%top},[<input_2=int32#3]
# asm 2: vld1.8 {>k0k1k2k3=d2->k0k1k2k3=d3},[<input_2=r2]
vld1.8 {d2-d3},[r2]

# qhasm: input_2 += 16
# asm 1: add <input_2=int32#3,<input_2=int32#3,#16
# asm 2: add <input_2=r2,<input_2=r2,#16
add r2,r2,#16

# qhasm: k4k5k6k7 = mem128[input_2]
# asm 1: vld1.8 {>k4k5k6k7=reg128#3%bot->k4k5k6k7=reg128#3%top},[<input_2=int32#3]
# asm 2: vld1.8 {>k4k5k6k7=d4->k4k5k6k7=d5},[<input_2=r2]
vld1.8 {d4-d5},[r2]

# qhasm: n1n2k6k1 = n1n2n3n0
# asm 1: vmov >n1n2k6k1=reg128#4,<n1n2n3n0=reg128#1
# asm 2: vmov >n1n2k6k1=q3,<n1n2n3n0=q0
vmov q3,q0

# qhasm: k2k3n3k7 = k0k1k2k3[2,3] k0k1k2k3[0,1]
# asm 1: vext.32 >k2k3n3k7=reg128#9,<k0k1k2k3=reg128#2,<k0k1k2k3=reg128#2,#2
# asm 2: vext.32 >k2k3n3k7=q8,<k0k1k2k3=q1,<k0k1k2k3=q1,#2
vext.32 q8,q1,q1,#2

# qhasm: k4k5k0n0 = k4k5k6k7
# asm 1: vmov >k4k5k0n0=reg128#10,<k4k5k6k7=reg128#3
# asm 2: vmov >k4k5k0n0=q9,<k4k5k6k7=q2
vmov q9,q2

# qhasm: n1n2k6k1 = n1n2k6k1[0,1] k0k1k2k3[1] k4k5k6k7[2]
# asm 1: vext.32 <n1n2k6k1=reg128#4%top,<k0k1k2k3=reg128#2%bot,<k4k5k6k7=reg128#3%top,#1
# asm 2: vext.32 <n1n2k6k1=d7,<k0k1k2k3=d2,<k4k5k6k7=d5,#1
vext.32 d7,d2,d5,#1

# qhasm: k2k3n3k7 = k2k3n3k7[0,1] k4k5k6k7[3] n1n2n3n0[2]
# asm 1: vext.32 <k2k3n3k7=reg128#9%top,<k4k5k6k7=reg128#3%top,<n1n2n3n0=reg128#1%top,#1
# asm 2: vext.32 <k2k3n3k7=d17,<k4k5k6k7=d5,<n1n2n3n0=d1,#1
vext.32 d17,d5,d1,#1

# qhasm: k4k5k0n0 = k4k5k0n0[0,1] n1n2n3n0[3] k0k1k2k3[0]
# asm 1: vext.32 <k4k5k0n0=reg128#10%top,<n1n2n3n0=reg128#1%top,<k0k1k2k3=reg128#2%bot,#1
# asm 2: vext.32 <k4k5k0n0=d19,<n1n2n3n0=d1,<k0k1k2k3=d2,#1
vext.32 d19,d1,d2,#1

# qhasm: n1n2k6k1 = n1n2k6k1[0,1] n1n2k6k1[3] n1n2k6k1[2]
# asm 1: vext.32 <n1n2k6k1=reg128#4%top,<n1n2k6k1=reg128#4%top,<n1n2k6k1=reg128#4%top,#1
# asm 2: vext.32 <n1n2k6k1=d7,<n1n2k6k1=d7,<n1n2k6k1=d7,#1
vext.32 d7,d7,d7,#1

# qhasm: k2k3n3k7 = k2k3n3k7[0,1] k2k3n3k7[3] k2k3n3k7[2]
# asm 1: vext.32 <k2k3n3k7=reg128#9%top,<k2k3n3k7=reg128#9%top,<k2k3n3k7=reg128#9%top,#1
# asm 2: vext.32 <k2k3n3k7=d17,<k2k3n3k7=d17,<k2k3n3k7=d17,#1
vext.32 d17,d17,d17,#1

# qhasm: k4k5k0n0 = k4k5k0n0[0,1] k4k5k0n0[3] k4k5k0n0[2]
# asm 1: vext.32 <k4k5k0n0=reg128#10%top,<k4k5k0n0=reg128#10%top,<k4k5k0n0=reg128#10%top,#1
# asm 2: vext.32 <k4k5k0n0=d19,<k4k5k0n0=d19,<k4k5k0n0=d19,#1
vext.32 d19,d19,d19,#1

# qhasm: diag0 = mem128[input_3]
# asm 1: vld1.8 {>diag0=reg128#1%bot->diag0=reg128#1%top},[<input_3=int32#4]
# asm 2: vld1.8 {>diag0=d0->diag0=d1},[<input_3=r3]
vld1.8 {d0-d1},[r3]

# qhasm: diag2 = n1n2k6k1[1,2,3] n1n2k6k1[0]
# asm 1: vext.32 >diag2=reg128#2,<n1n2k6k1=reg128#4,<n1n2k6k1=reg128#4,#1
# asm 2: vext.32 >diag2=q1,<n1n2k6k1=q3,<n1n2k6k1=q3,#1
vext.32 q1,q3,q3,#1

# qhasm: diag3 = k2k3n3k7[1,2,3] k2k3n3k7[0]
# asm 1: vext.32 >diag3=reg128#3,<k2k3n3k7=reg128#9,<k2k3n3k7=reg128#9,#1
# asm 2: vext.32 >diag3=q2,<k2k3n3k7=q8,<k2k3n3k7=q8,#1
vext.32 q2,q8,q8,#1

# qhasm: diag1 = k4k5k0n0[1,2,3] k4k5k0n0[0]
# asm 1: vext.32 >diag1=reg128#4,<k4k5k0n0=reg128#10,<k4k5k0n0=reg128#10,#1
# asm 2: vext.32 >diag1=q3,<k4k5k0n0=q9,<k4k5k0n0=q9,#1
vext.32 q3,q9,q9,#1

# qhasm: start0 = diag0
# asm 1: vmov >start0=reg128#9,<diag0=reg128#1
# asm 2: vmov >start0=q8,<diag0=q0
vmov q8,q0

# qhasm: start1 = diag1
# asm 1: vmov >start1=reg128#10,<diag1=reg128#4
# asm 2: vmov >start1=q9,<diag1=q3
vmov q9,q3

# qhasm: start2 = diag2
# asm 1: vmov >start2=reg128#11,<diag2=reg128#2
# asm 2: vmov >start2=q10,<diag2=q1
vmov q10,q1

# qhasm: start3 = diag3
# asm 1: vmov >start3=reg128#12,<diag3=reg128#3
# asm 2: vmov >start3=q11,<diag3=q2
vmov q11,q2

# qhasm: i = 20
# asm 1: ldr >i=int32#2,=20
# asm 2: ldr >i=r1,=20
ldr r1,=20

# qhasm: mainloop:
._mainloop:

# qhasm:   4x a0 = diag1 + diag0
# asm 1: vadd.i32 >a0=reg128#13,<diag1=reg128#4,<diag0=reg128#1
# asm 2: vadd.i32 >a0=q12,<diag1=q3,<diag0=q0
vadd.i32 q12,q3,q0

# qhasm:   4x b0 = a0 << 7
# asm 1: vshl.i32 >b0=reg128#14,<a0=reg128#13,#7
# asm 2: vshl.i32 >b0=q13,<a0=q12,#7
vshl.i32 q13,q12,#7

# qhasm:   4x b0 insert= a0 >> 25
# asm 1: vsri.i32 <b0=reg128#14,<a0=reg128#13,#25
# asm 2: vsri.i32 <b0=q13,<a0=q12,#25
vsri.i32 q13,q12,#25

# qhasm:      diag3 ^= b0
# asm 1: veor >diag3=reg128#3,<diag3=reg128#3,<b0=reg128#14
# asm 2: veor >diag3=q2,<diag3=q2,<b0=q13
veor q2,q2,q13

# qhasm:   4x a1 = diag0 + diag3
# asm 1: vadd.i32 >a1=reg128#13,<diag0=reg128#1,<diag3=reg128#3
# asm 2: vadd.i32 >a1=q12,<diag0=q0,<diag3=q2
vadd.i32 q12,q0,q2

# qhasm:   4x b1 = a1 << 9
# asm 1: vshl.i32 >b1=reg128#14,<a1=reg128#13,#9
# asm 2: vshl.i32 >b1=q13,<a1=q12,#9
vshl.i32 q13,q12,#9

# qhasm:   4x b1 insert= a1 >> 23
# asm 1: vsri.i32 <b1=reg128#14,<a1=reg128#13,#23
# asm 2: vsri.i32 <b1=q13,<a1=q12,#23
vsri.i32 q13,q12,#23

# qhasm:      diag2 ^= b1
# asm 1: veor >diag2=reg128#2,<diag2=reg128#2,<b1=reg128#14
# asm 2: veor >diag2=q1,<diag2=q1,<b1=q13
veor q1,q1,q13

# qhasm:   4x a2 = diag3 + diag2
# asm 1: vadd.i32 >a2=reg128#13,<diag3=reg128#3,<diag2=reg128#2
# asm 2: vadd.i32 >a2=q12,<diag3=q2,<diag2=q1
vadd.i32 q12,q2,q1

# qhasm:           diag3 = diag3[3] diag3[0,1,2]
# asm 1: vext.32 >diag3=reg128#3,<diag3=reg128#3,<diag3=reg128#3,#3
# asm 2: vext.32 >diag3=q2,<diag3=q2,<diag3=q2,#3
vext.32 q2,q2,q2,#3

# qhasm:   4x b2 = a2 << 13
# asm 1: vshl.i32 >b2=reg128#14,<a2=reg128#13,#13
# asm 2: vshl.i32 >b2=q13,<a2=q12,#13
vshl.i32 q13,q12,#13

# qhasm:   4x b2 insert= a2 >> 19
# asm 1: vsri.i32 <b2=reg128#14,<a2=reg128#13,#19
# asm 2: vsri.i32 <b2=q13,<a2=q12,#19
vsri.i32 q13,q12,#19

# qhasm:      diag1 ^= b2
# asm 1: veor >diag1=reg128#4,<diag1=reg128#4,<b2=reg128#14
# asm 2: veor >diag1=q3,<diag1=q3,<b2=q13
veor q3,q3,q13

# qhasm:   4x a3 = diag2 + diag1
# asm 1: vadd.i32 >a3=reg128#13,<diag2=reg128#2,<diag1=reg128#4
# asm 2: vadd.i32 >a3=q12,<diag2=q1,<diag1=q3
vadd.i32 q12,q1,q3

# qhasm:           diag2 = diag2[2,3] diag2[0,1]
# asm 1: vswp <diag2=reg128#2%bot,<diag2=reg128#2%top
# asm 2: vswp <diag2=d2,<diag2=d3
vswp d2,d3

# qhasm:   4x b3 = a3 << 18
# asm 1: vshl.i32 >b3=reg128#14,<a3=reg128#13,#18
# asm 2: vshl.i32 >b3=q13,<a3=q12,#18
vshl.i32 q13,q12,#18

# qhasm:   4x b3 insert= a3 >> 14
# asm 1: vsri.i32 <b3=reg128#14,<a3=reg128#13,#14
# asm 2: vsri.i32 <b3=q13,<a3=q12,#14
vsri.i32 q13,q12,#14

# qhasm:           diag1 = diag1[1,2,3] diag1[0]
# asm 1: vext.32 >diag1=reg128#4,<diag1=reg128#4,<diag1=reg128#4,#1
# asm 2: vext.32 >diag1=q3,<diag1=q3,<diag1=q3,#1
vext.32 q3,q3,q3,#1

# qhasm:      diag0 ^= b3
# asm 1: veor >diag0=reg128#1,<diag0=reg128#1,<b3=reg128#14
# asm 2: veor >diag0=q0,<diag0=q0,<b3=q13
veor q0,q0,q13

# qhasm:                  unsigned>? i -= 2
# asm 1: subs <i=int32#2,<i=int32#2,#2
# asm 2: subs <i=r1,<i=r1,#2
subs r1,r1,#2

# qhasm:   4x a0 = diag3 + diag0
# asm 1: vadd.i32 >a0=reg128#13,<diag3=reg128#3,<diag0=reg128#1
# asm 2: vadd.i32 >a0=q12,<diag3=q2,<diag0=q0
vadd.i32 q12,q2,q0

# qhasm:   4x b0 = a0 << 7
# asm 1: vshl.i32 >b0=reg128#14,<a0=reg128#13,#7
# asm 2: vshl.i32 >b0=q13,<a0=q12,#7
vshl.i32 q13,q12,#7

# qhasm:   4x b0 insert= a0 >> 25
# asm 1: vsri.i32 <b0=reg128#14,<a0=reg128#13,#25
# asm 2: vsri.i32 <b0=q13,<a0=q12,#25
vsri.i32 q13,q12,#25

# qhasm:      diag1 ^= b0
# asm 1: veor >diag1=reg128#4,<diag1=reg128#4,<b0=reg128#14
# asm 2: veor >diag1=q3,<diag1=q3,<b0=q13
veor q3,q3,q13

# qhasm:   4x a1 = diag0 + diag1
# asm 1: vadd.i32 >a1=reg128#13,<diag0=reg128#1,<diag1=reg128#4
# asm 2: vadd.i32 >a1=q12,<diag0=q0,<diag1=q3
vadd.i32 q12,q0,q3

# qhasm:   4x b1 = a1 << 9
# asm 1: vshl.i32 >b1=reg128#14,<a1=reg128#13,#9
# asm 2: vshl.i32 >b1=q13,<a1=q12,#9
vshl.i32 q13,q12,#9

# qhasm:   4x b1 insert= a1 >> 23
# asm 1: vsri.i32 <b1=reg128#14,<a1=reg128#13,#23
# asm 2: vsri.i32 <b1=q13,<a1=q12,#23
vsri.i32 q13,q12,#23

# qhasm:      diag2 ^= b1
# asm 1: veor >diag2=reg128#2,<diag2=reg128#2,<b1=reg128#14
# asm 2: veor >diag2=q1,<diag2=q1,<b1=q13
veor q1,q1,q13

# qhasm:   4x a2 = diag1 + diag2
# asm 1: vadd.i32 >a2=reg128#13,<diag1=reg128#4,<diag2=reg128#2
# asm 2: vadd.i32 >a2=q12,<diag1=q3,<diag2=q1
vadd.i32 q12,q3,q1

# qhasm:           diag1 = diag1[3] diag1[0,1,2]
# asm 1: vext.32 >diag1=reg128#4,<diag1=reg128#4,<diag1=reg128#4,#3
# asm 2: vext.32 >diag1=q3,<diag1=q3,<diag1=q3,#3
vext.32 q3,q3,q3,#3

# qhasm:   4x b2 = a2 << 13
# asm 1: vshl.i32 >b2=reg128#14,<a2=reg128#13,#13
# asm 2: vshl.i32 >b2=q13,<a2=q12,#13
vshl.i32 q13,q12,#13

# qhasm:   4x b2 insert= a2 >> 19
# asm 1: vsri.i32 <b2=reg128#14,<a2=reg128#13,#19
# asm 2: vsri.i32 <b2=q13,<a2=q12,#19
vsri.i32 q13,q12,#19

# qhasm:      diag3 ^= b2
# asm 1: veor >diag3=reg128#3,<diag3=reg128#3,<b2=reg128#14
# asm 2: veor >diag3=q2,<diag3=q2,<b2=q13
veor q2,q2,q13

# qhasm:   4x a3 = diag2 + diag3
# asm 1: vadd.i32 >a3=reg128#13,<diag2=reg128#2,<diag3=reg128#3
# asm 2: vadd.i32 >a3=q12,<diag2=q1,<diag3=q2
vadd.i32 q12,q1,q2

# qhasm:           diag2 = diag2[2,3] diag2[0,1]
# asm 1: vswp <diag2=reg128#2%bot,<diag2=reg128#2%top
# asm 2: vswp <diag2=d2,<diag2=d3
vswp d2,d3

# qhasm:   4x b3 = a3 << 18
# asm 1: vshl.i32 >b3=reg128#14,<a3=reg128#13,#18
# asm 2: vshl.i32 >b3=q13,<a3=q12,#18
vshl.i32 q13,q12,#18

# qhasm:   4x b3 insert= a3 >> 14
# asm 1: vsri.i32 <b3=reg128#14,<a3=reg128#13,#14
# asm 2: vsri.i32 <b3=q13,<a3=q12,#14
vsri.i32 q13,q12,#14

# qhasm:           diag3 = diag3[1,2,3] diag3[0]
# asm 1: vext.32 >diag3=reg128#3,<diag3=reg128#3,<diag3=reg128#3,#1
# asm 2: vext.32 >diag3=q2,<diag3=q2,<diag3=q2,#1
vext.32 q2,q2,q2,#1

# qhasm:      diag0 ^= b3
# asm 1: veor >diag0=reg128#1,<diag0=reg128#1,<b3=reg128#14
# asm 2: veor >diag0=q0,<diag0=q0,<b3=q13
veor q0,q0,q13

# qhasm: goto mainloop if unsigned>
bhi ._mainloop

# qhasm: 2x abab = 0xffffffff
# asm 1: vmov.i64 >abab=reg128#13,#0xffffffff
# asm 2: vmov.i64 >abab=q12,#0xffffffff
vmov.i64 q12,#0xffffffff

# qhasm: 4x x0x5x10x15 = diag0 + start0
# asm 1: vadd.i32 >x0x5x10x15=reg128#1,<diag0=reg128#1,<start0=reg128#9
# asm 2: vadd.i32 >x0x5x10x15=q0,<diag0=q0,<start0=q8
vadd.i32 q0,q0,q8

# qhasm: 4x x12x1x6x11 = diag1 + start1
# asm 1: vadd.i32 >x12x1x6x11=reg128#4,<diag1=reg128#4,<start1=reg128#10
# asm 2: vadd.i32 >x12x1x6x11=q3,<diag1=q3,<start1=q9
vadd.i32 q3,q3,q9

# qhasm: 4x x8x13x2x7 = diag2 + start2
# asm 1: vadd.i32 >x8x13x2x7=reg128#2,<diag2=reg128#2,<start2=reg128#11
# asm 2: vadd.i32 >x8x13x2x7=q1,<diag2=q1,<start2=q10
vadd.i32 q1,q1,q10

# qhasm: 4x x4x9x14x3 = diag3 + start3
# asm 1: vadd.i32 >x4x9x14x3=reg128#3,<diag3=reg128#3,<start3=reg128#12
# asm 2: vadd.i32 >x4x9x14x3=q2,<diag3=q2,<start3=q11
vadd.i32 q2,q2,q11

# qhasm: x0x1x10x11 = x0x5x10x15
# asm 1: vmov >x0x1x10x11=reg128#9,<x0x5x10x15=reg128#1
# asm 2: vmov >x0x1x10x11=q8,<x0x5x10x15=q0
vmov q8,q0

# qhasm: x12x13x6x7 = x12x1x6x11
# asm 1: vmov >x12x13x6x7=reg128#10,<x12x1x6x11=reg128#4
# asm 2: vmov >x12x13x6x7=q9,<x12x1x6x11=q3
vmov q9,q3

# qhasm: x8x9x2x3 = x8x13x2x7
# asm 1: vmov >x8x9x2x3=reg128#11,<x8x13x2x7=reg128#2
# asm 2: vmov >x8x9x2x3=q10,<x8x13x2x7=q1
vmov q10,q1

# qhasm: x4x5x14x15 = x4x9x14x3
# asm 1: vmov >x4x5x14x15=reg128#12,<x4x9x14x3=reg128#3
# asm 2: vmov >x4x5x14x15=q11,<x4x9x14x3=q2
vmov q11,q2

# qhasm: x0x1x10x11 = (abab & x0x1x10x11) | (~abab & x12x1x6x11)
# asm 1: vbif <x0x1x10x11=reg128#9,<x12x1x6x11=reg128#4,<abab=reg128#13
# asm 2: vbif <x0x1x10x11=q8,<x12x1x6x11=q3,<abab=q12
vbif q8,q3,q12

# qhasm: x12x13x6x7 = (abab & x12x13x6x7) | (~abab & x8x13x2x7)
# asm 1: vbif <x12x13x6x7=reg128#10,<x8x13x2x7=reg128#2,<abab=reg128#13
# asm 2: vbif <x12x13x6x7=q9,<x8x13x2x7=q1,<abab=q12
vbif q9,q1,q12

# qhasm: x8x9x2x3 = (abab & x8x9x2x3) | (~abab & x4x9x14x3)
# asm 1: vbif <x8x9x2x3=reg128#11,<x4x9x14x3=reg128#3,<abab=reg128#13
# asm 2: vbif <x8x9x2x3=q10,<x4x9x14x3=q2,<abab=q12
vbif q10,q2,q12

# qhasm: x4x5x14x15 = (abab & x4x5x14x15) | (~abab & x0x5x10x15)
# asm 1: vbif <x4x5x14x15=reg128#12,<x0x5x10x15=reg128#1,<abab=reg128#13
# asm 2: vbif <x4x5x14x15=q11,<x0x5x10x15=q0,<abab=q12
vbif q11,q0,q12

# qhasm: x0x1x2x3 = x0x1x10x11
# asm 1: vmov >x0x1x2x3=reg128#1,<x0x1x10x11=reg128#9
# asm 2: vmov >x0x1x2x3=q0,<x0x1x10x11=q8
vmov q0,q8

# qhasm: x4x5x6x7 = x4x5x14x15
# asm 1: vmov >x4x5x6x7=reg128#2,<x4x5x14x15=reg128#12
# asm 2: vmov >x4x5x6x7=q1,<x4x5x14x15=q11
vmov q1,q11

# qhasm: x8x9x10x11 = x8x9x2x3
# asm 1: vmov >x8x9x10x11=reg128#3,<x8x9x2x3=reg128#11
# asm 2: vmov >x8x9x10x11=q2,<x8x9x2x3=q10
vmov q2,q10

# qhasm: x12x13x14x15 = x12x13x6x7
# asm 1: vmov >x12x13x14x15=reg128#4,<x12x13x6x7=reg128#10
# asm 2: vmov >x12x13x14x15=q3,<x12x13x6x7=q9
vmov q3,q9

# qhasm: x0x1x2x3 = x0x1x2x3[0,1] x8x9x2x3[2,3]
# asm 1: vmov <x0x1x2x3=reg128#1%top,<x8x9x2x3=reg128#11%top
# asm 2: vmov <x0x1x2x3=d1,<x8x9x2x3=d21
vmov d1,d21

# qhasm: x4x5x6x7 = x4x5x6x7[0,1] x12x13x6x7[2,3]
# asm 1: vmov <x4x5x6x7=reg128#2%top,<x12x13x6x7=reg128#10%top
# asm 2: vmov <x4x5x6x7=d3,<x12x13x6x7=d19
vmov d3,d19

# qhasm: x8x9x10x11 = x8x9x10x11[0,1] x0x1x10x11[2,3]
# asm 1: vmov <x8x9x10x11=reg128#3%top,<x0x1x10x11=reg128#9%top
# asm 2: vmov <x8x9x10x11=d5,<x0x1x10x11=d17
vmov d5,d17

# qhasm: x12x13x14x15 = x12x13x14x15[0,1] x4x5x14x15[2,3]
# asm 1: vmov <x12x13x14x15=reg128#4%top,<x4x5x14x15=reg128#12%top
# asm 2: vmov <x12x13x14x15=d7,<x4x5x14x15=d23
vmov d7,d23

# qhasm: mem128[input_0] = x0x1x2x3
# asm 1: vst1.8 {<x0x1x2x3=reg128#1%bot-<x0x1x2x3=reg128#1%top},[<input_0=int32#1]
# asm 2: vst1.8 {<x0x1x2x3=d0-<x0x1x2x3=d1},[<input_0=r0]
vst1.8 {d0-d1},[r0]

# qhasm: input_0 += 16
# asm 1: add <input_0=int32#1,<input_0=int32#1,#16
# asm 2: add <input_0=r0,<input_0=r0,#16
add r0,r0,#16

# qhasm: mem128[input_0] = x4x5x6x7
# asm 1: vst1.8 {<x4x5x6x7=reg128#2%bot-<x4x5x6x7=reg128#2%top},[<input_0=int32#1]
# asm 2: vst1.8 {<x4x5x6x7=d2-<x4x5x6x7=d3},[<input_0=r0]
vst1.8 {d2-d3},[r0]

# qhasm: input_0 += 16
# asm 1: add <input_0=int32#1,<input_0=int32#1,#16
# asm 2: add <input_0=r0,<input_0=r0,#16
add r0,r0,#16

# qhasm: mem128[input_0] = x8x9x10x11
# asm 1: vst1.8 {<x8x9x10x11=reg128#3%bot-<x8x9x10x11=reg128#3%top},[<input_0=int32#1]
# asm 2: vst1.8 {<x8x9x10x11=d4-<x8x9x10x11=d5},[<input_0=r0]
vst1.8 {d4-d5},[r0]

# qhasm: input_0 += 16
# asm 1: add <input_0=int32#1,<input_0=int32#1,#16
# asm 2: add <input_0=r0,<input_0=r0,#16
add r0,r0,#16

# qhasm: mem128[input_0] = x12x13x14x15
# asm 1: vst1.8 {<x12x13x14x15=reg128#4%bot-<x12x13x14x15=reg128#4%top},[<input_0=int32#1]
# asm 2: vst1.8 {<x12x13x14x15=d6-<x12x13x14x15=d7},[<input_0=r0]
vst1.8 {d6-d7},[r0]

# qhasm: int32 result

# qhasm: result = 0
# asm 1: ldr >result=int32#1,=0
# asm 2: ldr >result=r0,=0
ldr r0,=0

# qhasm: return result
add sp,sp,#0
bx lr
