.arch armv6

SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_armv6
chacha_blocks_armv6_local:
tst r3, r3
beq .Lchacha_blocks_armv6_nobytes
stmfd sp!, {r4-r12, r14}
sub sp, sp, #192
str r0, [sp, #60]
str r1, [sp, #48]
str r2, [sp, #40]
str r3, [sp, #52]
add r1, sp, #64
ldr r4, =0x61707865
ldr r5, =0x3320646e
ldr r6, =0x79622d32
ldr r7, =0x6b206574
ldmia r0!, {r8-r11}
stmia r1!, {r4-r11}
ldmia r0!, {r4-r11}
stmia r1!, {r4-r11}
ldr r4, [r0]
str r4, [sp, #44]
.Lchacha_blocks_armv6_mainloop:
ldr r3, [sp, #52]
ldr r1, [sp, #48]
cmp r3, #64
bhs .Lchacha_blocks_armv6_noswap1
add r4, sp, #128
mov r5, r4
tst r1, r1
beq .Lchacha_blocks_armv6_nocopy1
.Lchacha_blocks_armv6_copyinput1:
subs r3, r3, #1
ldrb r0, [r1], #1
strb r0, [r4], #1
bne .Lchacha_blocks_armv6_copyinput1
str r5, [sp, #48]
.Lchacha_blocks_armv6_nocopy1:
ldr r4, [sp, #40]
str r5, [sp, #40]
str r4, [sp, #56]
.Lchacha_blocks_armv6_noswap1:
ldr r0, [sp, #44]
str r0, [sp, #0]
add r0, sp, #64
ldm r0, {r0-r12}
ldr r14, [sp, #(64 +60)]
str r6, [sp, #8]
str r11, [sp, #12]
str r14, [sp, #28]
ldr r11, [sp, #(64 +52)]
ldr r14, [sp, #(64 +56)]
.Lchacha_blocks_armv6_rounds:
ldr r6, [sp, #0]
add r0, r0, r4
add r1, r1, r5
eor r12, r12, r0
eor r11, r11, r1
ror r12, r12, #16
ror r11, r11, #16
subs r6, r6, #2
add r8, r8, r12
add r9, r9, r11
eor r4, r4, r8
eor r5, r5, r9
str r6, [sp, #0]
ror r4, r4, #20
ror r5, r5, #20
add r0, r0, r4
add r1, r1, r5
ldr r6, [sp, #8]
eor r12, r12, r0
eor r11, r11, r1
ror r12, r12, #24
ror r11, r11, #24
add r8, r8, r12
add r9, r9, r11
eor r4, r4, r8
eor r5, r5, r9
str r11, [sp, #20]
ror r4, r4, #25
ror r5, r5, #25
str r4, [sp, #4]
ldr r4, [sp, #28]
add r2, r2, r6
add r3, r3, r7
ldr r11, [sp, #12]
eor r14, r14, r2
eor r4, r4, r3
ror r14, r14, #16
ror r4, r4, #16
add r10, r10, r14
add r11, r11, r4
eor r6, r6, r10
eor r7, r7, r11
ror r6, r6, #20
ror r7, r7, #20
add r2, r2, r6
add r3, r3, r7
eor r14, r14, r2
eor r4, r4, r3
ror r14, r14, #24
ror r4, r4, #24
add r10, r10, r14
add r11, r11, r4
eor r6, r6, r10
eor r7, r7, r11
ror r6, r6, #25
ror r7, r7, #25
add r0, r0, r5
add r1, r1, r6
eor r4, r4, r0
eor r12, r12, r1
ror r4, r4, #16
ror r12, r12, #16
add r10, r10, r4
add r11, r11, r12
eor r5, r5, r10
eor r6, r6, r11
ror r5, r5, #20
ror r6, r6, #20
add r0, r0, r5
add r1, r1, r6
eor r4, r4, r0
eor r12, r12, r1
ror r4, r4, #24
ror r12, r12, #24
add r10, r10, r4
add r11, r11, r12
eor r5, r5, r10
eor r6, r6, r11
str r11, [sp, #12]
ror r5, r5, #25
ror r6, r6, #25
str r4, [sp, #28]
ldr r4, [sp, #4]
add r2, r2, r7
add r3, r3, r4
ldr r11, [sp, #20]
eor r11, r11, r2
eor r14, r14, r3
ror r11, r11, #16
ror r14, r14, #16
add r8, r8, r11
add r9, r9, r14
eor r7, r7, r8
eor r4, r4, r9
ror r7, r7, #20
ror r4, r4, #20
str r6, [sp, #8]
add r2, r2, r7
add r3, r3, r4
eor r11, r11, r2
eor r14, r14, r3
ror r11, r11, #24
ror r14, r14, #24
add r8, r8, r11
add r9, r9, r14
eor r7, r7, r8
eor r4, r4, r9
ror r7, r7, #25
ror r4, r4, #25
bne .Lchacha_blocks_armv6_rounds
str r8, [sp, #0]
str r9, [sp, #4]
str r10, [sp, #8]
str r12, [sp, #16]
str r11, [sp, #20]
str r14, [sp, #24]
ldr r12, [sp, #48]
ldr r14, [sp, #40]
ldr r8, [sp, #(64 +0)]
ldr r9, [sp, #(64 +4)]
ldr r10, [sp, #(64 +8)]
ldr r11, [sp, #(64 +12)]
add r0, r0, r8
add r1, r1, r9
add r2, r2, r10
ldr r8, [sp, #(64 +16)]
add r3, r3, r11
ldr r9, [sp, #(64 +20)]
add r4, r4, r8
ldr r10, [sp, #(64 +24)]
add r5, r5, r9
ldr r11, [sp, #(64 +28)]
add r6, r6, r10
tst r12, r12
add r7, r7, r11
beq .Lchacha_blocks_armv6_nomessage1
ldmia r12!, {r8-r11}
eor r0, r0, r8
eor r1, r1, r9
eor r2, r2, r10
ldr r8, [r12, #0]
eor r3, r3, r11
ldr r9, [r12, #4]
eor r4, r4, r8
ldr r10, [r12, #8]
eor r5, r5, r9
ldr r11, [r12, #12]
eor r6, r6, r10
add r12, r12, #16
eor r7, r7, r11
.Lchacha_blocks_armv6_nomessage1:
stmia r14!, {r0-r7}
ldm sp, {r0-r7}
ldr r8, [sp, #(64 +32)]
ldr r9, [sp, #(64 +36)]
ldr r10, [sp, #(64 +40)]
ldr r11, [sp, #(64 +44)]
add r0, r0, r8
add r1, r1, r9
add r2, r2, r10
ldr r8, [sp, #(64 +48)]
add r3, r3, r11
ldr r9, [sp, #(64 +52)]
add r4, r4, r8
ldr r10, [sp, #(64 +56)]
add r5, r5, r9
ldr r11, [sp, #(64 +60)]
add r6, r6, r10
adds r8, r8, #1
add r7, r7, r11
adc r9, r9, #0
tst r12, r12
str r8, [sp, #(64 +48)]
str r9, [sp, #(64 +52)]
beq .Lchacha_blocks_armv6_nomessage2
ldmia r12!, {r8-r11}
eor r0, r0, r8
eor r1, r1, r9
eor r2, r2, r10
ldr r8, [r12, #0]
eor r3, r3, r11
ldr r9, [r12, #4]
eor r4, r4, r8
ldr r10, [r12, #8]
eor r5, r5, r9
ldr r11, [r12, #12]
eor r6, r6, r10
add r12, r12, #16
eor r7, r7, r11
.Lchacha_blocks_armv6_nomessage2:
stmia r14!, {r0-r7}
str r12, [sp, #48]
str r14, [sp, #40]
ldr r3, [sp, #52]
cmp r3, #64
sub r4, r3, #64
str r4, [sp, #52]
bhi .Lchacha_blocks_armv6_mainloop
cmp r3, #64
beq .Lchacha_blocks_armv6_nocopy2
ldr r1, [sp, #56]
sub r14, r14, #64
.Lchacha_blocks_armv6_copyinput2:
subs r3, r3, #1
ldrb r0, [r14], #1
strb r0, [r1], #1
bne .Lchacha_blocks_armv6_copyinput2
.Lchacha_blocks_armv6_nocopy2:
ldr r7, [sp, #60]
ldr r8, [sp, #(64 +48)]
ldr r9, [sp, #(64 +52)]
str r8, [r7, #32]
str r9, [r7, #36]
mov r12, sp
stmia r12!, {r0-r7}
add r12, r12, #48
stmia r12!, {r0-r7}
add sp, sp, #192
ldmfd sp!, {r4-r12, r14}
.Lchacha_blocks_armv6_nobytes:
bx lr
FN_END chacha_blocks_armv6

.ltorg

GLOBAL_HIDDEN_FN hchacha_armv6
hchacha_armv6_local:
stmfd sp!, {r4-r12, r14}
sub sp, sp, #32
str r2, [sp, #20]
str r3, [sp, #24]
ldr r12, [r1, #0]
ldr r11, [r1, #4]
ldr r14, [r1, #8]
ldr r4, [r1, #12]
str r11, [sp, #4]
str r4, [sp, #16]
ldmia r0, {r4-r11}
str r4, [sp, #8]
str r6, [sp, #0]
str r11, [sp, #12]
ldr r11, [sp, #4]
ldr r0, =0x61707865
ldr r1, =0x3320646e
ldr r2, =0x79622d32
ldr r3, =0x6b206574
.Lhchacha_armv6_mainloop:
ldr r6, [sp, #24]
subs r6, r6, #2
str r6, [sp, #24]
ldr r6, [sp, #0]
add r0, r0, r4
add r1, r1, r5
eor r12, r12, r0
eor r11, r11, r1
ror r12, r12, #16
ror r11, r11, #16
add r8, r8, r12
add r9, r9, r11
eor r4, r4, r8
eor r5, r5, r9
ror r4, r4, #20
ror r5, r5, #20
add r0, r0, r4
add r1, r1, r5
eor r12, r12, r0
eor r11, r11, r1
ror r12, r12, #24
ror r11, r11, #24
add r8, r8, r12
add r9, r9, r11
eor r4, r4, r8
eor r5, r5, r9
ror r4, r4, #25
ror r5, r5, #25
str r11, [sp, #4]
str r4, [sp, #8]
ldr r11, [sp, #12]
ldr r4, [sp, #16]
add r2, r2, r6
add r3, r3, r7
eor r14, r14, r2
eor r4, r4, r3
ror r14, r14, #16
ror r4, r4, #16
add r10, r10, r14
add r11, r11, r4
eor r6, r6, r10
eor r7, r7, r11
ror r6, r6, #20
ror r7, r7, #20
add r2, r2, r6
add r3, r3, r7
eor r14, r14, r2
eor r4, r4, r3
ror r14, r14, #24
ror r4, r4, #24
add r10, r10, r14
add r11, r11, r4
eor r6, r6, r10
eor r7, r7, r11
ror r6, r6, #25
ror r7, r7, #25
add r0, r0, r5
add r1, r1, r6
eor r4, r4, r0
eor r12, r12, r1
ror r4, r4, #16
ror r12, r12, #16
add r10, r10, r4
add r11, r11, r12
eor r5, r5, r10
eor r6, r6, r11
ror r5, r5, #20
ror r6, r6, #20
add r0, r0, r5
add r1, r1, r6
eor r4, r4, r0
eor r12, r12, r1
ror r4, r4, #24
ror r12, r12, #24
add r10, r10, r4
add r11, r11, r12
eor r5, r5, r10
eor r6, r6, r11
ror r5, r5, #25
ror r6, r6, #25
str r11, [sp, #12]
str r4, [sp, #16]
ldr r11, [sp, #4]
ldr r4, [sp, #8]
add r2, r2, r7
add r3, r3, r4
eor r11, r11, r2
eor r14, r14, r3
ror r11, r11, #16
ror r14, r14, #16
add r8, r8, r11
add r9, r9, r14
eor r7, r7, r8
eor r4, r4, r9
ror r7, r7, #20
ror r4, r4, #20
add r2, r2, r7
add r3, r3, r4
eor r11, r11, r2
eor r14, r14, r3
ror r11, r11, #24
ror r14, r14, #24
add r8, r8, r11
add r9, r9, r14
eor r7, r7, r8
eor r4, r4, r9
ror r7, r7, #25
ror r4, r4, #25
str r6, [sp, #0]
bne .Lhchacha_armv6_mainloop
stm sp, {r0-r3}
ldr r8, [sp, #20]
mov r4, r12
mov r5, r11
mov r6, r14
ldr r7, [sp, #16]
stmia r8, {r0-r7}
add sp, sp, #32
ldmfd sp!, {r4-r12, r14}
bx lr
FN_END hchacha_armv6

.ltorg

GLOBAL_HIDDEN_FN chacha_armv6
stmfd sp!, {r4-r7, lr}
mov r12, sp
sub sp, sp, #64
and sp, sp, #0xffffff80
ldmia r0!, {r4-r7}
stmia sp!, {r4-r7}
ldmia r0!, {r4-r7}
stmia sp!, {r4-r7}
eor r4, r4, r4
eor r5, r5, r5
mov r7, r12
stmia sp!, {r4-r5}
ldmia r1!, {r4-r5}
stmia sp!, {r4-r5}
ldr r4, [r7, #24]
str r4, [sp]
sub sp, sp, #48
mov r0, sp
mov r1, r2
mov r2, r3
ldr r3, [r7, #20]
bl chacha_blocks_armv6_local
eor r0, r0, r0
eor r1, r1, r1
eor r2, r2, r2
eor r3, r3, r3
stmia sp!, {r0-r3}
stmia sp!, {r0-r3}
stmia sp!, {r0-r3}
mov sp, r7
ldmfd sp!, {r4-r7, lr}
bx lr
FN_END chacha_armv6


GLOBAL_HIDDEN_FN xchacha_armv6
stmfd sp!, {r4-r6, lr}
mov r7, sp
sub sp, sp, #64
and sp, sp, #0xffffff80
mov r4, r2
mov r5, r3
add r6, r1, #16
mov r2, sp
ldr r3, [r7, #20]
bl hchacha_armv6_local
eor r0, r0, r0
eor r1, r1, r1
add sp, sp, #32
stmia sp!, {r0-r1}
ldm r6, {r0-r1}
stmia sp!, {r0-r1}
ldr r2, [r7, #20]
str r2, [sp]
sub sp, sp, #48
mov r0, sp
mov r1, r4
mov r2, r5
ldr r3, [r7, #16]
bl chacha_blocks_armv6_local
eor r0, r0, r0
eor r1, r1, r1
eor r2, r2, r2
eor r3, r3, r3
stmia sp!, {r0-r3}
stmia sp!, {r0-r3}
stmia sp!, {r0-r3}
mov sp, r7
ldmfd sp!, {r4-r6, lr}
bx lr
FN_END xchacha_armv6

