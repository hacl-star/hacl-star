.p2align 5

.global _cbdeta4
.global cbdeta4
_cbdeta4:
cbdeta4:

vmovupd _mask11(%rip),%ymm0
vmovupd _mask0f(%rip),%ymm1
vmovupd _16xq(%rip),%ymm2

mov  $256,%rdx

._looptop:

vmovupd   0(%rsi),%ymm3

vpand %ymm3,%ymm0,%ymm4

vpsrlw $1,%ymm3,%ymm3

vpand %ymm3,%ymm0,%ymm5

vpaddb %ymm5,%ymm4,%ymm4

vpsrlw $1,%ymm3,%ymm3

vpand %ymm3,%ymm0,%ymm5

vpaddb %ymm5,%ymm4,%ymm4

vpsrlw $1,%ymm3,%ymm3

vpand %ymm3,%ymm0,%ymm3

vpaddb %ymm3,%ymm4,%ymm3

vpsrlw $4,%ymm3,%ymm4

vpand %ymm3,%ymm1,%ymm3

vpand %ymm4,%ymm1,%ymm4

vpsubb %ymm4,%ymm3,%ymm3

vpmovsxbw %xmm3,%ymm4

vpaddw %ymm2,%ymm4,%ymm4

vmovupd   %ymm4,0(%rdi)

vperm2f128 $0x21,%ymm3,%ymm3,%ymm3

vpmovsxbw %xmm3,%ymm4

vpaddw %ymm2,%ymm4,%ymm4

vmovupd   %ymm4,32(%rdi)

add  $64,%rdi
add  $32,%rsi
sub  $32,%rdx

ja ._looptop

ret
