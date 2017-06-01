#include "x86.inc"

SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_avx
chacha_blocks_avx_local:
pushl %ebp
movl %esp, %ebp
andl $-64, %esp
pushl %esi
pushl %edi
pushl %ebx
subl $1268, %esp
LOAD_VAR_PIC chacha_constants, %eax
vmovdqa 0(%eax), %xmm5
vmovdqa 16(%eax), %xmm2
vmovdqa 32(%eax), %xmm1
movl $1, %edx
movl 20(%ebp), %ebx
movl 16(%ebp), %esi
movl %esi, %ecx
movl 12(%ebp), %eax
vmovd %edx, %xmm0
testl %ebx, %ebx
je chacha_blocks_avx_30
movl 8(%ebp), %edi
vmovdqu (%edi), %xmm7
vmovdqu 16(%edi), %xmm6
vmovdqu 32(%edi), %xmm4
movl 48(%edi), %edx
cmpl $256, %ebx
jb chacha_blocks_avx_10
movl 8(%ebp), %edi
movl %ebx, 44(%esp)
vpshufd $0, %xmm5, %xmm3
movl 32(%edi), %ebx
vmovdqu %xmm3, 368(%esp)
vpshufd $85, %xmm5, %xmm3
vmovdqu %xmm3, 352(%esp)
vpshufd $170, %xmm5, %xmm3
vmovdqu %xmm3, 336(%esp)
vpshufd $255, %xmm5, %xmm3
vmovdqu %xmm3, 320(%esp)
vpshufd $0, %xmm7, %xmm3
movl %ebx, 32(%esp)
vmovdqu %xmm3, 304(%esp)
vpshufd $85, %xmm7, %xmm3
movl 36(%edi), %ebx
vmovdqu %xmm3, 288(%esp)
vpshufd $170, %xmm7, %xmm3
vmovdqu %xmm3, 272(%esp)
vpshufd $255, %xmm7, %xmm3
vmovdqu %xmm3, 256(%esp)
vpshufd $0, %xmm6, %xmm3
vmovdqu %xmm3, 240(%esp)
vpshufd $85, %xmm6, %xmm3
vmovdqu %xmm3, 224(%esp)
vpshufd $170, %xmm6, %xmm3
movl %ebx, 36(%esp)
vmovdqu %xmm3, 208(%esp)
vpshufd $255, %xmm6, %xmm3
movl 40(%edi), %ebx
vmovdqu %xmm3, 192(%esp)
vpshufd $170, %xmm4, %xmm3
movl 44(%edi), %edi
vmovdqu %xmm3, 176(%esp)
vpshufd $255, %xmm4, %xmm3
movl %ebx, 24(%esp)
movl %edx, 432(%esp)
movl %ecx, 40(%esp)
movl %edi, 28(%esp)
movl 32(%esp), %edx
movl 36(%esp), %ecx
vmovdqu %xmm6, 128(%esp)
vmovdqu %xmm7, 112(%esp)
vmovdqu %xmm5, 96(%esp)
vmovdqu %xmm3, 384(%esp)
vmovdqu %xmm0, 80(%esp)
vmovdqu %xmm1, 448(%esp)
vmovdqu %xmm2, 464(%esp)
jmp chacha_blocks_avx_4
.p2align 6,,63
nop;nop;nop;nop;nop;nop;nop;nop;
chacha_blocks_avx_4:
movl %edx, %ebx
movl %ecx, %edi
addl $1, %ebx
movl %ebx, 148(%esp)
movl %edx, %ebx
adcl $0, %edi
addl $2, %ebx
movl %edi, 164(%esp)
movl %ecx, %edi
movl %ebx, 152(%esp)
movl %edx, %ebx
adcl $0, %edi
addl $3, %ebx
movl %edx, 144(%esp)
movl %ebx, 156(%esp)
vmovdqu 144(%esp), %xmm3
vmovdqu 272(%esp), %xmm7
movl %edi, 168(%esp)
movl %ecx, %edi
vmovdqu %xmm3, 400(%esp)
adcl $0, %edi
vmovdqu %xmm7, 592(%esp)
addl $4, %edx
vmovdqu %xmm3, 608(%esp)
vmovdqu 208(%esp), %xmm7
vmovdqu 176(%esp), %xmm3
movl %ecx, 160(%esp)
adcl $0, %ecx
movl %edi, 172(%esp)
vmovdqu 352(%esp), %xmm5
vmovdqu 336(%esp), %xmm0
vmovdqu 320(%esp), %xmm1
vmovdqu 288(%esp), %xmm2
vmovdqu %xmm7, 496(%esp)
vmovdqu %xmm3, 624(%esp)
vmovdqu 160(%esp), %xmm6
vmovdqu 368(%esp), %xmm4
vmovdqu 192(%esp), %xmm7
vmovdqu 384(%esp), %xmm3
vmovdqu %xmm5, 544(%esp)
vmovdqu %xmm0, 560(%esp)
vmovdqu %xmm1, 576(%esp)
vmovdqu %xmm2, 640(%esp)
vmovdqu %xmm6, 416(%esp)
vmovdqu 304(%esp), %xmm5
vmovdqu 256(%esp), %xmm2
vmovdqu 240(%esp), %xmm1
vmovdqu 224(%esp), %xmm0
movl 432(%esp), %ebx
vmovdqu %xmm7, 480(%esp)
vmovdqu %xmm3, 512(%esp)
vmovdqu %xmm4, 528(%esp)
chacha_blocks_avx_5:
vpaddd 528(%esp), %xmm5, %xmm4
vmovdqu 640(%esp), %xmm7
vpxor 608(%esp), %xmm4, %xmm3
vmovdqu %xmm4, 672(%esp)
vpaddd 544(%esp), %xmm7, %xmm7
vmovdqu 464(%esp), %xmm4
vpxor %xmm7, %xmm6, %xmm6
vpshufb %xmm4, %xmm3, %xmm3
vpshufb %xmm4, %xmm6, %xmm6
vmovdqu %xmm7, 688(%esp)
vpaddd %xmm3, %xmm1, %xmm1
vmovdqu 592(%esp), %xmm7
vpaddd %xmm6, %xmm0, %xmm0
vpaddd 560(%esp), %xmm7, %xmm7
vpxor %xmm1, %xmm5, %xmm5
vmovdqu %xmm2, 656(%esp)
vpaddd 576(%esp), %xmm2, %xmm2
vmovdqu %xmm7, 704(%esp)
vpxor 624(%esp), %xmm7, %xmm7
vmovdqu %xmm2, 720(%esp)
vpxor 512(%esp), %xmm2, %xmm2
vpshufb %xmm4, %xmm7, %xmm7
vpshufb %xmm4, %xmm2, %xmm2
vmovdqu %xmm0, 768(%esp)
vpslld $12, %xmm5, %xmm4
vmovdqu %xmm1, 752(%esp)
vpsrld $20, %xmm5, %xmm1
vpxor 640(%esp), %xmm0, %xmm0
vpxor %xmm4, %xmm1, %xmm5
vpsrld $20, %xmm0, %xmm1
vpslld $12, %xmm0, %xmm0
vpxor %xmm0, %xmm1, %xmm1
vpaddd 496(%esp), %xmm7, %xmm0
vpaddd 480(%esp), %xmm2, %xmm4
vmovdqu %xmm2, 736(%esp)
vpxor 592(%esp), %xmm0, %xmm2
vmovdqu %xmm0, 800(%esp)
vmovdqu %xmm4, 816(%esp)
vpxor 656(%esp), %xmm4, %xmm0
vpsrld $20, %xmm2, %xmm4
vpslld $12, %xmm2, %xmm2
vpxor %xmm2, %xmm4, %xmm4
vpsrld $20, %xmm0, %xmm2
vpslld $12, %xmm0, %xmm0
vpxor %xmm0, %xmm2, %xmm0
vpaddd 672(%esp), %xmm5, %xmm2
vmovdqu %xmm2, 848(%esp)
vpxor %xmm2, %xmm3, %xmm2
vmovdqu 448(%esp), %xmm3
vpshufb %xmm3, %xmm2, %xmm2
vmovdqu %xmm5, 784(%esp)
vpaddd 688(%esp), %xmm1, %xmm5
vmovdqu %xmm2, 880(%esp)
vpxor %xmm5, %xmm6, %xmm6
vmovdqu %xmm5, 864(%esp)
vpaddd 720(%esp), %xmm0, %xmm2
vpaddd 704(%esp), %xmm4, %xmm5
vpshufb %xmm3, %xmm6, %xmm6
vmovdqu %xmm2, 928(%esp)
vpxor %xmm5, %xmm7, %xmm7
vpxor 736(%esp), %xmm2, %xmm2
vmovdqu %xmm5, 912(%esp)
vpshufb %xmm3, %xmm7, %xmm5
vpshufb %xmm3, %xmm2, %xmm2
vmovdqu 880(%esp), %xmm3
vpaddd 752(%esp), %xmm3, %xmm7
vmovdqu %xmm4, 832(%esp)
vmovdqu %xmm6, 896(%esp)
vpaddd 768(%esp), %xmm6, %xmm6
vpxor 784(%esp), %xmm7, %xmm4
vmovdqu %xmm6, 976(%esp)
vpxor %xmm6, %xmm1, %xmm6
vpsrld $25, %xmm4, %xmm1
vpslld $7, %xmm4, %xmm3
vmovdqu %xmm5, 944(%esp)
vmovdqu %xmm7, 960(%esp)
vpxor %xmm3, %xmm1, %xmm7
vpaddd 800(%esp), %xmm5, %xmm5
vpsrld $25, %xmm6, %xmm1
vpslld $7, %xmm6, %xmm6
vpaddd 816(%esp), %xmm2, %xmm3
vpxor %xmm6, %xmm1, %xmm4
vpxor 832(%esp), %xmm5, %xmm1
vpxor %xmm3, %xmm0, %xmm0
vpsrld $25, %xmm1, %xmm6
vpslld $7, %xmm1, %xmm1
vmovdqu %xmm3, 1024(%esp)
vpsrld $25, %xmm0, %xmm3
vpslld $7, %xmm0, %xmm0
vpxor %xmm1, %xmm6, %xmm1
vpxor %xmm0, %xmm3, %xmm6
vpaddd 848(%esp), %xmm4, %xmm0
vmovdqu %xmm4, 1008(%esp)
vpxor %xmm0, %xmm2, %xmm3
vpaddd 864(%esp), %xmm1, %xmm4
vmovdqu 464(%esp), %xmm2
vmovdqu %xmm4, 1072(%esp)
vmovdqu %xmm0, 1056(%esp)
vpshufb %xmm2, %xmm3, %xmm0
vpxor 880(%esp), %xmm4, %xmm4
vpaddd %xmm0, %xmm5, %xmm5
vpshufb %xmm2, %xmm4, %xmm4
vpaddd 912(%esp), %xmm6, %xmm3
vmovdqu %xmm6, 1040(%esp)
vpaddd 928(%esp), %xmm7, %xmm6
vmovdqu %xmm7, 992(%esp)
vpxor 896(%esp), %xmm3, %xmm7
vmovdqu %xmm6, 1104(%esp)
vpxor 944(%esp), %xmm6, %xmm6
vpshufb %xmm2, %xmm7, %xmm7
vmovdqu %xmm3, 1088(%esp)
vpshufb %xmm2, %xmm6, %xmm3
vmovdqu %xmm5, 1136(%esp)
vpaddd 1024(%esp), %xmm4, %xmm2
vpxor 1008(%esp), %xmm5, %xmm5
vpxor %xmm2, %xmm1, %xmm1
vmovdqu %xmm2, 1152(%esp)
vpsrld $20, %xmm5, %xmm6
vpslld $12, %xmm5, %xmm2
vpxor %xmm2, %xmm6, %xmm5
vpsrld $20, %xmm1, %xmm6
vpslld $12, %xmm1, %xmm1
vpaddd 960(%esp), %xmm7, %xmm2
vpxor %xmm1, %xmm6, %xmm1
vpaddd 976(%esp), %xmm3, %xmm6
vmovdqu %xmm3, 1120(%esp)
vpxor 1040(%esp), %xmm2, %xmm3
vmovdqu %xmm2, 1184(%esp)
vmovdqu %xmm6, 1200(%esp)
vpxor 992(%esp), %xmm6, %xmm2
vpsrld $20, %xmm3, %xmm6
vpslld $12, %xmm3, %xmm3
vpxor %xmm3, %xmm6, %xmm6
vpsrld $20, %xmm2, %xmm3
vpslld $12, %xmm2, %xmm2
vmovdqu %xmm5, 1168(%esp)
vpxor %xmm2, %xmm3, %xmm2
vpaddd 1056(%esp), %xmm5, %xmm5
vpaddd 1072(%esp), %xmm1, %xmm3
vmovdqu %xmm5, 528(%esp)
vpxor %xmm5, %xmm0, %xmm5
vmovdqu 448(%esp), %xmm0
vpxor %xmm3, %xmm4, %xmm4
vpshufb %xmm0, %xmm5, %xmm5
vpshufb %xmm0, %xmm4, %xmm4
vmovdqu %xmm6, 1216(%esp)
vpaddd 1088(%esp), %xmm6, %xmm6
vmovdqu %xmm3, 544(%esp)
vpxor %xmm6, %xmm7, %xmm7
vpaddd 1104(%esp), %xmm2, %xmm3
vmovdqu %xmm6, 560(%esp)
vpshufb %xmm0, %xmm7, %xmm6
vpxor 1120(%esp), %xmm3, %xmm7
vmovdqu %xmm4, 608(%esp)
vmovdqu %xmm3, 576(%esp)
vpshufb %xmm0, %xmm7, %xmm0
vpaddd 1136(%esp), %xmm5, %xmm3
vpaddd 1152(%esp), %xmm4, %xmm4
vmovdqu %xmm5, 512(%esp)
vpxor %xmm4, %xmm1, %xmm1
vpxor 1168(%esp), %xmm3, %xmm5
vmovdqu %xmm3, 496(%esp)
vpsrld $25, %xmm5, %xmm7
vpslld $7, %xmm5, %xmm3
vpsrld $25, %xmm1, %xmm5
vpslld $7, %xmm1, %xmm1
vpxor %xmm1, %xmm5, %xmm1
vmovdqu %xmm0, 624(%esp)
vmovdqu %xmm1, 592(%esp)
vpaddd 1184(%esp), %xmm6, %xmm1
vpaddd 1200(%esp), %xmm0, %xmm0
vmovdqu %xmm4, 480(%esp)
vpxor %xmm3, %xmm7, %xmm4
vpxor 1216(%esp), %xmm1, %xmm3
vpxor %xmm0, %xmm2, %xmm7
vmovdqu %xmm4, 640(%esp)
vpsrld $25, %xmm3, %xmm2
vpslld $7, %xmm3, %xmm3
vpsrld $25, %xmm7, %xmm4
vpslld $7, %xmm7, %xmm5
vpxor %xmm3, %xmm2, %xmm2
vpxor %xmm5, %xmm4, %xmm5
addl $-2, %ebx
jne chacha_blocks_avx_5
vmovdqu 528(%esp), %xmm4
testl %eax, %eax
je chacha_blocks_avx_37
vmovdqu %xmm6, 64(%esp)
vmovdqu 544(%esp), %xmm6
vpaddd 368(%esp), %xmm4, %xmm3
vmovdqu 560(%esp), %xmm7
vmovdqu 576(%esp), %xmm4
vmovdqu %xmm0, 48(%esp)
vpaddd 352(%esp), %xmm6, %xmm0
vpaddd 336(%esp), %xmm7, %xmm6
vpaddd 320(%esp), %xmm4, %xmm7
vpunpckldq %xmm0, %xmm3, %xmm4
vpunpckhdq %xmm0, %xmm3, %xmm0
vpunpckldq %xmm7, %xmm6, %xmm3
vpunpckhdq %xmm7, %xmm6, %xmm7
vpunpcklqdq %xmm3, %xmm4, %xmm6
vpunpckhqdq %xmm3, %xmm4, %xmm4
vpxor 64(%eax), %xmm4, %xmm3
vpunpcklqdq %xmm7, %xmm0, %xmm4
vpunpckhqdq %xmm7, %xmm0, %xmm7
vpxor (%eax), %xmm6, %xmm6
vpxor 128(%eax), %xmm4, %xmm4
vpxor 192(%eax), %xmm7, %xmm0
vmovdqu %xmm6, (%esi)
vmovdqu %xmm4, 128(%esi)
vmovdqu %xmm3, 64(%esi)
vmovdqu %xmm0, 192(%esi)
vpaddd 304(%esp), %xmm5, %xmm6
vmovdqu 640(%esp), %xmm5
vpaddd 288(%esp), %xmm5, %xmm4
vmovdqu 592(%esp), %xmm5
vpaddd 272(%esp), %xmm5, %xmm7
vpaddd 256(%esp), %xmm2, %xmm3
vpunpckldq %xmm4, %xmm6, %xmm0
vpunpckldq %xmm3, %xmm7, %xmm5
vpunpckhdq %xmm4, %xmm6, %xmm2
vpunpckhdq %xmm3, %xmm7, %xmm3
vpunpcklqdq %xmm5, %xmm0, %xmm6
vpunpckhqdq %xmm5, %xmm0, %xmm7
vpunpcklqdq %xmm3, %xmm2, %xmm5
vpunpckhqdq %xmm3, %xmm2, %xmm2
vpxor 16(%eax), %xmm6, %xmm4
vpxor 144(%eax), %xmm5, %xmm6
vpxor 208(%eax), %xmm2, %xmm5
vpaddd 240(%esp), %xmm1, %xmm2
vmovdqu 48(%esp), %xmm1
vpxor 80(%eax), %xmm7, %xmm0
vmovdqu %xmm6, 144(%esi)
vmovdqu %xmm5, 208(%esi)
vmovdqu %xmm0, 80(%esi)
vmovdqu %xmm4, 16(%esi)
vpaddd 224(%esp), %xmm1, %xmm6
vmovdqu 496(%esp), %xmm1
vmovdqu 480(%esp), %xmm5
vpaddd 208(%esp), %xmm1, %xmm0
vpaddd 192(%esp), %xmm5, %xmm3
vpunpckldq %xmm6, %xmm2, %xmm7
vpunpckhdq %xmm6, %xmm2, %xmm2
vpunpckldq %xmm3, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm0, %xmm5
vpunpcklqdq %xmm6, %xmm7, %xmm4
vpunpckhqdq %xmm6, %xmm7, %xmm0
vpunpcklqdq %xmm5, %xmm2, %xmm3
vpunpckhqdq %xmm5, %xmm2, %xmm7
vpxor 32(%eax), %xmm4, %xmm1
vpxor 96(%eax), %xmm0, %xmm4
vpxor 160(%eax), %xmm3, %xmm6
vpxor 224(%eax), %xmm7, %xmm5
vmovdqu %xmm1, 32(%esi)
vmovdqu %xmm4, 96(%esi)
vmovdqu %xmm6, 160(%esi)
vmovdqu %xmm5, 224(%esi)
vmovdqu 608(%esp), %xmm1
vmovdqu 64(%esp), %xmm2
vmovdqu 624(%esp), %xmm0
vmovdqu 512(%esp), %xmm3
vpaddd 400(%esp), %xmm1, %xmm7
vpaddd 416(%esp), %xmm2, %xmm1
vpaddd 176(%esp), %xmm0, %xmm2
vpaddd 384(%esp), %xmm3, %xmm0
vpunpckldq %xmm1, %xmm7, %xmm6
vpunpckldq %xmm0, %xmm2, %xmm4
vpunpckhdq %xmm1, %xmm7, %xmm5
vpunpckhdq %xmm0, %xmm2, %xmm2
vpunpcklqdq %xmm4, %xmm6, %xmm3
vpxor 48(%eax), %xmm3, %xmm1
vpunpckhqdq %xmm4, %xmm6, %xmm0
vpunpcklqdq %xmm2, %xmm5, %xmm3
vpunpckhqdq %xmm2, %xmm5, %xmm5
vpxor 112(%eax), %xmm0, %xmm4
vpxor 176(%eax), %xmm3, %xmm6
vpxor 240(%eax), %xmm5, %xmm7
addl $256, %eax
vmovdqu %xmm1, 48(%esi)
vmovdqu %xmm4, 112(%esi)
vmovdqu %xmm6, 176(%esi)
vmovdqu %xmm7, 240(%esi)
jmp chacha_blocks_avx_8
chacha_blocks_avx_37:
vmovdqu %xmm2, 656(%esp)
vmovdqu %xmm1, (%esp)
vmovdqu %xmm0, 48(%esp)
vmovdqu 544(%esp), %xmm1
vmovdqu 560(%esp), %xmm2
vmovdqu 576(%esp), %xmm0
vmovdqu %xmm6, 64(%esp)
vpaddd 368(%esp), %xmm4, %xmm7
vpaddd 352(%esp), %xmm1, %xmm6
vpaddd 336(%esp), %xmm2, %xmm3
vpaddd 320(%esp), %xmm0, %xmm0
vpunpckldq %xmm6, %xmm7, %xmm1
vpunpckldq %xmm0, %xmm3, %xmm2
vpunpcklqdq %xmm2, %xmm1, %xmm4
vpunpckhqdq %xmm2, %xmm1, %xmm2
vpunpckhdq %xmm6, %xmm7, %xmm6
vpunpckhdq %xmm0, %xmm3, %xmm3
vpunpcklqdq %xmm3, %xmm6, %xmm7
vpunpckhqdq %xmm3, %xmm6, %xmm1
vmovdqu %xmm4, (%esi)
vmovdqu %xmm2, 64(%esi)
vmovdqu %xmm7, 128(%esi)
vmovdqu %xmm1, 192(%esi)
vmovdqu 640(%esp), %xmm4
vmovdqu 592(%esp), %xmm2
vmovdqu 656(%esp), %xmm0
vpaddd 304(%esp), %xmm5, %xmm5
vpaddd 288(%esp), %xmm4, %xmm1
vpaddd 272(%esp), %xmm2, %xmm7
vpaddd 256(%esp), %xmm0, %xmm3
vpunpckldq %xmm1, %xmm5, %xmm4
vpunpckldq %xmm3, %xmm7, %xmm2
vpunpcklqdq %xmm2, %xmm4, %xmm6
vpunpckhqdq %xmm2, %xmm4, %xmm4
vpunpckhdq %xmm1, %xmm5, %xmm5
vpunpckhdq %xmm3, %xmm7, %xmm1
vpunpcklqdq %xmm1, %xmm5, %xmm2
vpunpckhqdq %xmm1, %xmm5, %xmm5
vmovdqu %xmm6, 16(%esi)
vmovdqu %xmm4, 80(%esi)
vmovdqu %xmm2, 144(%esi)
vmovdqu %xmm5, 208(%esi)
vmovdqu (%esp), %xmm0
vmovdqu 48(%esp), %xmm4
vmovdqu 496(%esp), %xmm3
vmovdqu 480(%esp), %xmm6
vpaddd 240(%esp), %xmm0, %xmm0
vpaddd 224(%esp), %xmm4, %xmm2
vpaddd 208(%esp), %xmm3, %xmm5
vpaddd 192(%esp), %xmm6, %xmm7
vpunpckldq %xmm2, %xmm0, %xmm4
vpunpckldq %xmm7, %xmm5, %xmm3
vpunpcklqdq %xmm3, %xmm4, %xmm1
vpunpckhqdq %xmm3, %xmm4, %xmm6
vpunpckhdq %xmm2, %xmm0, %xmm2
vpunpckhdq %xmm7, %xmm5, %xmm7
vmovdqu 64(%esp), %xmm0
vpunpcklqdq %xmm7, %xmm2, %xmm5
vpunpckhqdq %xmm7, %xmm2, %xmm2
vmovdqu %xmm1, 32(%esi)
vmovdqu %xmm6, 96(%esi)
vmovdqu %xmm2, 224(%esi)
vmovdqu %xmm5, 160(%esi)
vmovdqu 608(%esp), %xmm1
vmovdqu 624(%esp), %xmm6
vmovdqu 512(%esp), %xmm7
vpaddd 416(%esp), %xmm0, %xmm3
vpaddd 400(%esp), %xmm1, %xmm4
vpaddd 176(%esp), %xmm6, %xmm2
vpaddd 384(%esp), %xmm7, %xmm0
vpunpckldq %xmm3, %xmm4, %xmm5
vpunpckldq %xmm0, %xmm2, %xmm6
vpunpckhdq %xmm3, %xmm4, %xmm3
vpunpckhdq %xmm0, %xmm2, %xmm4
vpunpcklqdq %xmm6, %xmm5, %xmm1
vpunpckhqdq %xmm6, %xmm5, %xmm5
vpunpcklqdq %xmm4, %xmm3, %xmm0
vpunpckhqdq %xmm4, %xmm3, %xmm2
vmovdqu %xmm1, 48(%esi)
vmovdqu %xmm5, 112(%esi)
vmovdqu %xmm0, 176(%esi)
vmovdqu %xmm2, 240(%esi)
chacha_blocks_avx_8:
movl 44(%esp), %ebx
addl $256, %esi
addl $-256, %ebx
movl %ebx, 44(%esp)
cmpl $256, %ebx
jae chacha_blocks_avx_4
movl %edx, 32(%esp)
movl %edx, %edi
movl %ecx, 36(%esp)
movl %edi, 16(%esp)
movl %ecx, %edi
movl %edi, 20(%esp)
vmovdqu 128(%esp), %xmm6
vmovdqu 112(%esp), %xmm7
vmovdqu 96(%esp), %xmm5
vmovdqu 80(%esp), %xmm0
vmovdqu 448(%esp), %xmm1
vmovdqu 464(%esp), %xmm2
movl 432(%esp), %edx
movl 40(%esp), %ecx
vmovdqu 16(%esp), %xmm4
chacha_blocks_avx_10:
movl %ebx, %edi
testl %ebx, %ebx
jne chacha_blocks_avx_12
chacha_blocks_avx_11:
movl 8(%ebp), %eax
vmovdqu %xmm4, 32(%eax)
addl $1268, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx_12:
movl $0, 20(%esp)
movl %ecx, 40(%esp)
vmovdqu %xmm0, 80(%esp)
vmovdqu %xmm1, 448(%esp)
vmovdqu %xmm2, 464(%esp)
movl %edi, 36(%esp)
movl %ebx, 44(%esp)
movl %edx, 432(%esp)
movl 20(%esp), %ecx
jmp chacha_blocks_avx_13
chacha_blocks_avx_29:
movl %edx, 44(%esp)
addl $64, %esi
chacha_blocks_avx_13:
incl %ecx
movl %ecx, %edx
shll $6, %edx
negl %edx
addl 36(%esp), %edx
lea 64(%edx), %ebx
cmpl $64, %ebx
jae chacha_blocks_avx_24
testl %eax, %eax
je chacha_blocks_avx_23
testl %ebx, %ebx
je chacha_blocks_avx_22
movl %ebx, %edi
shrl $1, %edi
movl %edi, 24(%esp)
testl %edi, %edi
jbe chacha_blocks_avx_31
movl %esi, 32(%esp)
xorl %edi, %edi
movl %edx, 16(%esp)
movl %ecx, 20(%esp)
movl 24(%esp), %esi
chacha_blocks_avx_18:
movzbl (%eax,%edi,2), %edx
movb %dl, 192(%esp,%edi,2)
movzbl 1(%eax,%edi,2), %ecx
movb %cl, 193(%esp,%edi,2)
incl %edi
cmpl %esi, %edi
jb chacha_blocks_avx_18
movl 16(%esp), %edx
lea 1(%edi,%edi), %edi
movl 20(%esp), %ecx
movl 32(%esp), %esi
movl %edi, 28(%esp)
chacha_blocks_avx_20:
lea -1(%edi), %edi
cmpl %ebx, %edi
jae chacha_blocks_avx_22
movzbl (%edi,%eax), %eax
movl 28(%esp), %edi
movb %al, 191(%esp,%edi)
chacha_blocks_avx_22:
lea 192(%esp), %eax
chacha_blocks_avx_23:
movl %esi, 40(%esp)
lea 192(%esp), %esi
chacha_blocks_avx_24:
vmovdqu %xmm5, 96(%esp)
vmovdqa %xmm5, %xmm0
vmovdqu %xmm4, (%esp)
vmovdqa %xmm7, %xmm3
movl %esi, 32(%esp)
xorl %edi, %edi
vmovdqu %xmm6, 128(%esp)
vmovdqa %xmm6, %xmm2
vmovdqu %xmm7, 112(%esp)
vmovdqa %xmm4, %xmm1
movl %eax, 48(%esp)
vmovdqu 448(%esp), %xmm4
vmovdqu 464(%esp), %xmm5
movl 432(%esp), %esi
chacha_blocks_avx_25:
vpaddd %xmm3, %xmm0, %xmm6
incl %edi
vpxor %xmm6, %xmm1, %xmm0
vpshufb %xmm5, %xmm0, %xmm1
vpaddd %xmm1, %xmm2, %xmm0
lea (%edi,%edi), %eax
vpxor %xmm0, %xmm3, %xmm2
vpsrld $20, %xmm2, %xmm3
vpslld $12, %xmm2, %xmm7
vpxor %xmm7, %xmm3, %xmm7
vpaddd %xmm7, %xmm6, %xmm3
vpxor %xmm3, %xmm1, %xmm1
vpshufb %xmm4, %xmm1, %xmm2
vpaddd %xmm2, %xmm0, %xmm6
vpxor %xmm6, %xmm7, %xmm0
vpsrld $25, %xmm0, %xmm1
vpslld $7, %xmm0, %xmm7
vpshufd $147, %xmm3, %xmm3
vpxor %xmm7, %xmm1, %xmm1
vpshufd $78, %xmm2, %xmm2
vpaddd %xmm1, %xmm3, %xmm0
vpxor %xmm0, %xmm2, %xmm2
vpshufb %xmm5, %xmm2, %xmm7
vpshufd $57, %xmm6, %xmm6
vpaddd %xmm7, %xmm6, %xmm3
vpxor %xmm3, %xmm1, %xmm2
vpsrld $20, %xmm2, %xmm1
vpslld $12, %xmm2, %xmm6
vpxor %xmm6, %xmm1, %xmm2
vpaddd %xmm2, %xmm0, %xmm1
vpxor %xmm1, %xmm7, %xmm0
vpshufb %xmm4, %xmm0, %xmm7
vpaddd %xmm7, %xmm3, %xmm3
vpxor %xmm3, %xmm2, %xmm6
vpshufd $57, %xmm1, %xmm0
vpshufd $78, %xmm7, %xmm1
vpslld $7, %xmm6, %xmm7
vpshufd $147, %xmm3, %xmm2
vpsrld $25, %xmm6, %xmm3
vpxor %xmm7, %xmm3, %xmm3
cmpl %esi, %eax
jne chacha_blocks_avx_25
vmovdqu 128(%esp), %xmm6
vmovdqu 112(%esp), %xmm7
vpaddd %xmm6, %xmm2, %xmm2
vmovdqu 96(%esp), %xmm5
vpaddd %xmm7, %xmm3, %xmm3
vmovdqu (%esp), %xmm4
vpaddd %xmm5, %xmm0, %xmm0
movl 48(%esp), %eax
vpaddd %xmm4, %xmm1, %xmm1
movl 32(%esp), %esi
testl %eax, %eax
je chacha_blocks_avx_28
vpxor (%eax), %xmm0, %xmm0
vpxor 16(%eax), %xmm3, %xmm3
vpxor 32(%eax), %xmm2, %xmm2
vpxor 48(%eax), %xmm1, %xmm1
addl $64, %eax
chacha_blocks_avx_28:
vmovdqu %xmm0, (%esi)
vmovdqu %xmm3, 16(%esi)
vmovdqu %xmm2, 32(%esi)
vmovdqu %xmm1, 48(%esi)
vpaddq 80(%esp), %xmm4, %xmm4
cmpl $64, %ebx
jbe chacha_blocks_avx_32
jmp chacha_blocks_avx_29
chacha_blocks_avx_30:
addl $1268, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx_31:
movl $1, %edi
movl %edi, 28(%esp)
jmp chacha_blocks_avx_20
chacha_blocks_avx_32:
movl 44(%esp), %ebx
movl 40(%esp), %ecx
cmpl $64, %ebx
jae chacha_blocks_avx_11
testl %ebx, %ebx
jbe chacha_blocks_avx_11
xorl %edx, %edx
chacha_blocks_avx_35:
movzbl (%edx,%esi), %eax
movb %al, (%edx,%ecx)
incl %edx
cmpl %ebx, %edx
jb chacha_blocks_avx_35
jmp chacha_blocks_avx_11
FN_END chacha_blocks_avx


GLOBAL_HIDDEN_FN hchacha_avx
hchacha_avx_local:
LOAD_VAR_PIC chacha_constants, %eax
vmovdqa 0(%eax), %xmm0
vmovdqa 16(%eax), %xmm6
vmovdqa 32(%eax), %xmm5
movl 4(%esp), %eax
movl 8(%esp), %edx
vmovdqu 0(%eax), %xmm1
vmovdqu 16(%eax), %xmm2
vmovdqu 0(%edx), %xmm3
movl 12(%esp), %edx
movl 16(%esp), %ecx
hhacha_mainloop_avx:
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm6, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $12, %xmm1, %xmm4
vpsrld $20, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm5, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $7, %xmm1, %xmm4
vpsrld $25, %xmm1, %xmm1
vpshufd $0x93, %xmm0, %xmm0
vpxor %xmm1, %xmm4, %xmm1
vpshufd $0x4e, %xmm3, %xmm3
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm6, %xmm3, %xmm3
vpshufd $0x39, %xmm2, %xmm2
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpslld $12, %xmm1, %xmm4
vpsrld $20, %xmm1, %xmm1
vpxor %xmm1, %xmm4, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vpshufb %xmm5, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpshufd $0x39, %xmm0, %xmm0
vpslld $7, %xmm1, %xmm4
vpshufd $0x4e, %xmm3, %xmm3
vpsrld $25, %xmm1, %xmm1
vpshufd $0x93, %xmm2, %xmm2
vpxor %xmm1, %xmm4, %xmm1
subl $2, %ecx
jne hhacha_mainloop_avx
vmovdqu %xmm0, (%edx)
vmovdqu %xmm3, 16(%edx)
ret
FN_END hchacha_avx

GLOBAL_HIDDEN_FN chacha_avx
pushl %ebp
pushl %ebx
movl %esp, %ebp
subl $64, %esp
andl $~63, %esp
movl %esp, %ebx
movl 12(%ebp), %ecx
xorl %edx, %edx
vmovdqu 0(%ecx), %xmm0
vmovdqu 16(%ecx), %xmm1
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm1, 16(%ebx)
movl 16(%ebp), %ecx
movl %edx, 32(%ebx)
movl %edx, 36(%ebx)
movl 0(%ecx), %eax
movl 4(%ecx), %edx
movl %eax, 40(%ebx)
movl %edx, 44(%ebx)
movl 32(%ebp), %eax
movl %eax, 48(%ebx)
pushl 28(%ebp)
pushl 24(%ebp)
pushl 20(%ebp)
pushl %ebx
call chacha_blocks_avx_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm0, 16(%ebx)
vmovdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END chacha_avx

GLOBAL_HIDDEN_FN xchacha_avx
pushl %ebp
pushl %ebx
movl %esp, %ebp
subl $64, %esp
andl $~63, %esp
movl %esp, %ebx
pushl 32(%ebp)
pushl %ebx
pushl 16(%ebp)
pushl 12(%ebp)
call hchacha_avx_local
xorl %edx, %edx
movl 16(%ebp), %ecx
movl 32(%ebx), %edx
movl 36(%ebx), %edx
movl 16(%ecx), %eax
movl %eax, 40(%ebx)
movl 20(%ecx), %eax
movl %eax, 44(%ebx)
movl 32(%ebp), %eax
movl %eax, 48(%ebx)
pushl 28(%ebp)
pushl 24(%ebp)
pushl 20(%ebp)
pushl %ebx
call chacha_blocks_avx_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm0, 16(%ebx)
vmovdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END xchacha_avx

SECTION_RODATA

.p2align 4,,15
chacha_constants:
.long 0x61707865,0x3320646e,0x79622d32,0x6b206574 /* "expand 32-byte k" */
.byte 2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13       /* pshufb rotate by 16 */
.byte 3,0,1,2,7,4,5,6,11,8,9,10,15,12,13,14       /* pshufb rotate by 8 */



