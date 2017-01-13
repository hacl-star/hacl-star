SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_avx
chacha_blocks_avx_local:
pushl %ebp
movl %esp, %ebp
andl $~63, %esp
pushl %esi
pushl %edi
pushl %ebx
subl $1268, %esp
movl $1, %ecx
LOAD_VAR_PIC chacha_constants, %esi
movl 16(%ebp), %edx
movl 20(%ebp), %ebx
vmovd %ecx, %xmm2
vmovdqu 16(%esi), %xmm0
vmovdqu 32(%esi), %xmm1
movl 12(%ebp), %eax
vmovdqu %xmm0, 448(%esp)
vmovdqu %xmm1, 432(%esp)
vmovdqu %xmm2, 96(%esp)
movl %edx, 416(%esp)
testl %ebx, %ebx
je chacha_blocks_avx_36
chacha_blocks_avx_2:
movl 8(%ebp), %ecx
vmovdqu 0(%esi), %xmm0
vmovdqu (%ecx), %xmm1
vmovdqu 16(%ecx), %xmm2
movl 48(%ecx), %edi
vmovdqu %xmm0, 48(%esp)
movl %edi, 424(%esp)
vmovdqu %xmm1, 64(%esp)
vmovdqu %xmm2, 80(%esp)
vmovdqu 32(%ecx), %xmm0
cmpl $256, %ebx
jb chacha_blocks_avx_10
chacha_blocks_avx_3:
vmovdqu 64(%esp), %xmm7
vpshufd $255, %xmm7, %xmm1
vmovdqu %xmm1, 208(%esp)
vmovdqu 80(%esp), %xmm1
vmovdqu 48(%esp), %xmm4
vpshufd $0, %xmm7, %xmm2
vmovdqu %xmm2, 240(%esp)
vpshufd $85, %xmm7, %xmm3
vpshufd $170, %xmm7, %xmm2
vpshufd $0, %xmm1, %xmm7
vmovdqu %xmm7, 192(%esp)
vpshufd $85, %xmm1, %xmm7
vpshufd $85, %xmm4, %xmm5
vmovdqu %xmm7, 176(%esp)
vpshufd $170, %xmm1, %xmm7
vpshufd $255, %xmm1, %xmm1
vpshufd $0, %xmm4, %xmm6
vmovdqu %xmm5, 224(%esp)
vpshufd $170, %xmm4, %xmm5
vpshufd $255, %xmm4, %xmm4
vmovdqu %xmm1, 144(%esp)
vpshufd $170, %xmm0, %xmm1
vpshufd $255, %xmm0, %xmm0
movl 32(%ecx), %edi
movl 36(%ecx), %esi
vmovdqu %xmm7, 160(%esp)
vmovdqu %xmm1, 128(%esp)
vmovdqu %xmm0, 256(%esp)
vmovdqu %xmm2, 336(%esp)
vmovdqu %xmm3, 320(%esp)
vmovdqu %xmm4, 304(%esp)
vmovdqu %xmm5, 288(%esp)
vmovdqu %xmm6, 272(%esp)
movl %ebx, 420(%esp)
chacha_blocks_avx_4:
movl %edi, %ecx
movl %esi, %ebx
addl $1, %ecx
movl %ecx, 36(%esp)
movl %edi, %ecx
adcl $0, %ebx
addl $2, %ecx
movl %ebx, 116(%esp)
movl %esi, %ebx
movl %ecx, 40(%esp)
movl %edi, %ecx
adcl $0, %ebx
addl $3, %ecx
movl %edi, 32(%esp)
movl %ecx, 44(%esp)
vmovdqu 32(%esp), %xmm4
vmovdqu 320(%esp), %xmm7
vmovdqu 240(%esp), %xmm1
movl %ebx, 120(%esp)
movl %esi, %ebx
vmovdqu %xmm4, 368(%esp)
adcl $0, %ebx
vmovdqu %xmm4, 464(%esp)
addl $4, %edi
vmovdqu 304(%esp), %xmm0
vmovdqu 128(%esp), %xmm4
vmovdqu %xmm7, 560(%esp)
vmovdqu %xmm1, 384(%esp)
vmovdqu 160(%esp), %xmm7
vmovdqu 208(%esp), %xmm1
movl %esi, 112(%esp)
adcl $0, %esi
movl %ebx, 124(%esp)
vmovdqu %xmm0, 576(%esp)
vmovdqu %xmm4, 480(%esp)
vmovdqu 272(%esp), %xmm5
vmovdqu 336(%esp), %xmm0
vmovdqu 256(%esp), %xmm4
vmovdqu %xmm7, 528(%esp)
vmovdqu 112(%esp), %xmm6
vmovdqu 224(%esp), %xmm3
vmovdqu 288(%esp), %xmm2
vmovdqu 144(%esp), %xmm7
vmovdqu %xmm1, 592(%esp)
vmovdqu %xmm0, 544(%esp)
vmovdqu %xmm4, 496(%esp)
vmovdqu %xmm5, 608(%esp)
vmovdqu %xmm6, 352(%esp)
vmovdqu 192(%esp), %xmm1
vmovdqu 176(%esp), %xmm0
movl 424(%esp), %ecx
vmovdqu 592(%esp), %xmm5
vmovdqu 384(%esp), %xmm4
vmovdqu %xmm7, 512(%esp)
vmovdqu %xmm2, 640(%esp)
vmovdqu %xmm3, 624(%esp)
jmp chacha_blocks_avx_5
.p2align 5
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
chacha_blocks_avx_5:
vpaddd 608(%esp), %xmm4, %xmm2
vmovdqu 560(%esp), %xmm7
vpxor 464(%esp), %xmm2, %xmm3
vmovdqu %xmm2, 656(%esp)
vpaddd 624(%esp), %xmm7, %xmm7
vmovdqu 448(%esp), %xmm2
vpxor %xmm7, %xmm6, %xmm6
vpshufb %xmm2, %xmm3, %xmm3
vpshufb %xmm2, %xmm6, %xmm6
vmovdqu %xmm7, 672(%esp)
vpaddd %xmm3, %xmm1, %xmm1
vmovdqu 544(%esp), %xmm7
vpaddd %xmm6, %xmm0, %xmm0
vpaddd 640(%esp), %xmm7, %xmm7
vpxor %xmm1, %xmm4, %xmm4
vmovdqu %xmm5, 592(%esp)
vpaddd 576(%esp), %xmm5, %xmm5
vmovdqu %xmm7, 688(%esp)
vpxor 480(%esp), %xmm7, %xmm7
vmovdqu %xmm5, 704(%esp)
vpxor 496(%esp), %xmm5, %xmm5
vpshufb %xmm2, %xmm7, %xmm7
vpshufb %xmm2, %xmm5, %xmm5
vmovdqu %xmm0, 752(%esp)
vpslld $12, %xmm4, %xmm2
vmovdqu %xmm1, 736(%esp)
vpsrld $20, %xmm4, %xmm1
vpxor 560(%esp), %xmm0, %xmm0
vpor %xmm2, %xmm1, %xmm4
vpsrld $20, %xmm0, %xmm1
vpslld $12, %xmm0, %xmm0
vpor %xmm0, %xmm1, %xmm1
vpaddd 528(%esp), %xmm7, %xmm0
vpaddd 512(%esp), %xmm5, %xmm2
vmovdqu %xmm5, 720(%esp)
vpxor 544(%esp), %xmm0, %xmm5
vmovdqu %xmm0, 784(%esp)
vmovdqu %xmm2, 800(%esp)
vpxor 592(%esp), %xmm2, %xmm0
vpsrld $20, %xmm5, %xmm2
vpslld $12, %xmm5, %xmm5
vpor %xmm5, %xmm2, %xmm2
vpsrld $20, %xmm0, %xmm5
vpslld $12, %xmm0, %xmm0
vpor %xmm0, %xmm5, %xmm0
vpaddd 656(%esp), %xmm4, %xmm5
vmovdqu %xmm5, 832(%esp)
vpxor %xmm5, %xmm3, %xmm5
vmovdqu 432(%esp), %xmm3
vpshufb %xmm3, %xmm5, %xmm5
vmovdqu %xmm4, 768(%esp)
vpaddd 672(%esp), %xmm1, %xmm4
vmovdqu %xmm5, 864(%esp)
vpxor %xmm4, %xmm6, %xmm6
vmovdqu %xmm4, 848(%esp)
vpaddd 704(%esp), %xmm0, %xmm5
vpaddd 688(%esp), %xmm2, %xmm4
vpshufb %xmm3, %xmm6, %xmm6
vmovdqu %xmm5, 912(%esp)
vpxor %xmm4, %xmm7, %xmm7
vpxor 720(%esp), %xmm5, %xmm5
vmovdqu %xmm4, 896(%esp)
vpshufb %xmm3, %xmm7, %xmm4
vpshufb %xmm3, %xmm5, %xmm5
vmovdqu 864(%esp), %xmm3
vpaddd 736(%esp), %xmm3, %xmm7
vmovdqu %xmm2, 816(%esp)
vmovdqu %xmm6, 880(%esp)
vpaddd 752(%esp), %xmm6, %xmm6
vpxor 768(%esp), %xmm7, %xmm2
vmovdqu %xmm6, 960(%esp)
vpxor %xmm6, %xmm1, %xmm6
vpsrld $25, %xmm2, %xmm1
vpslld $7, %xmm2, %xmm3
vmovdqu %xmm4, 928(%esp)
vmovdqu %xmm7, 944(%esp)
vpor %xmm3, %xmm1, %xmm7
vpaddd 784(%esp), %xmm4, %xmm4
vpsrld $25, %xmm6, %xmm1
vpslld $7, %xmm6, %xmm6
vpaddd 800(%esp), %xmm5, %xmm3
vpor %xmm6, %xmm1, %xmm2
vpxor 816(%esp), %xmm4, %xmm1
vpxor %xmm3, %xmm0, %xmm0
vpsrld $25, %xmm1, %xmm6
vpslld $7, %xmm1, %xmm1
vmovdqu %xmm3, 1008(%esp)
vpsrld $25, %xmm0, %xmm3
vpslld $7, %xmm0, %xmm0
vpor %xmm1, %xmm6, %xmm1
vpor %xmm0, %xmm3, %xmm6
vpaddd 832(%esp), %xmm2, %xmm0
vmovdqu %xmm2, 992(%esp)
vpxor %xmm0, %xmm5, %xmm3
vpaddd 848(%esp), %xmm1, %xmm2
vmovdqu 448(%esp), %xmm5
vmovdqu %xmm2, 1056(%esp)
vmovdqu %xmm0, 1040(%esp)
vpshufb %xmm5, %xmm3, %xmm0
vpxor 864(%esp), %xmm2, %xmm2
vpaddd %xmm0, %xmm4, %xmm4
vpshufb %xmm5, %xmm2, %xmm2
vpaddd 896(%esp), %xmm6, %xmm3
vmovdqu %xmm6, 1024(%esp)
vpaddd 912(%esp), %xmm7, %xmm6
vmovdqu %xmm7, 976(%esp)
vpxor 880(%esp), %xmm3, %xmm7
vmovdqu %xmm6, 1088(%esp)
vpxor 928(%esp), %xmm6, %xmm6
vpshufb %xmm5, %xmm7, %xmm7
vmovdqu %xmm3, 1072(%esp)
vpshufb %xmm5, %xmm6, %xmm3
vmovdqu %xmm4, 1120(%esp)
vpaddd 1008(%esp), %xmm2, %xmm5
vpxor 992(%esp), %xmm4, %xmm4
vpxor %xmm5, %xmm1, %xmm1
vmovdqu %xmm5, 1136(%esp)
vpsrld $20, %xmm4, %xmm6
vpslld $12, %xmm4, %xmm5
vpor %xmm5, %xmm6, %xmm4
vpsrld $20, %xmm1, %xmm6
vpslld $12, %xmm1, %xmm1
vpaddd 944(%esp), %xmm7, %xmm5
vpor %xmm1, %xmm6, %xmm1
vpaddd 960(%esp), %xmm3, %xmm6
vmovdqu %xmm3, 1104(%esp)
vpxor 1024(%esp), %xmm5, %xmm3
vmovdqu %xmm5, 1168(%esp)
vmovdqu %xmm6, 1184(%esp)
vpxor 976(%esp), %xmm6, %xmm5
vpsrld $20, %xmm3, %xmm6
vpslld $12, %xmm3, %xmm3
vpor %xmm3, %xmm6, %xmm6
vpsrld $20, %xmm5, %xmm3
vpslld $12, %xmm5, %xmm5
vmovdqu %xmm4, 1152(%esp)
vpor %xmm5, %xmm3, %xmm5
vpaddd 1040(%esp), %xmm4, %xmm4
vpaddd 1056(%esp), %xmm1, %xmm3
vmovdqu %xmm4, 608(%esp)
vpxor %xmm4, %xmm0, %xmm4
vmovdqu 432(%esp), %xmm0
vpxor %xmm3, %xmm2, %xmm2
vpshufb %xmm0, %xmm4, %xmm4
vpshufb %xmm0, %xmm2, %xmm2
vmovdqu %xmm6, 1200(%esp)
vpaddd 1072(%esp), %xmm6, %xmm6
vmovdqu %xmm3, 624(%esp)
vpxor %xmm6, %xmm7, %xmm7
vpaddd 1088(%esp), %xmm5, %xmm3
vmovdqu %xmm6, 640(%esp)
vpshufb %xmm0, %xmm7, %xmm6
vpxor 1104(%esp), %xmm3, %xmm7
vmovdqu %xmm2, 464(%esp)
vmovdqu %xmm3, 576(%esp)
vpshufb %xmm0, %xmm7, %xmm0
vpaddd 1120(%esp), %xmm4, %xmm3
vpaddd 1136(%esp), %xmm2, %xmm2
vmovdqu %xmm4, 496(%esp)
vpxor %xmm2, %xmm1, %xmm1
vpxor 1152(%esp), %xmm3, %xmm4
vmovdqu %xmm2, 512(%esp)
vpsrld $25, %xmm4, %xmm7
vpslld $7, %xmm4, %xmm2
vpsrld $25, %xmm1, %xmm4
vpslld $7, %xmm1, %xmm1
vpor %xmm1, %xmm4, %xmm1
vmovdqu %xmm0, 480(%esp)
vmovdqu %xmm1, 544(%esp)
vpaddd 1168(%esp), %xmm6, %xmm1
vpaddd 1184(%esp), %xmm0, %xmm0
vmovdqu %xmm3, 528(%esp)
vpor %xmm2, %xmm7, %xmm3
vpxor 1200(%esp), %xmm1, %xmm2
vpxor %xmm0, %xmm5, %xmm7
vmovdqu %xmm3, 560(%esp)
vpsrld $25, %xmm2, %xmm5
vpslld $7, %xmm2, %xmm2
vpsrld $25, %xmm7, %xmm3
vpslld $7, %xmm7, %xmm4
vpor %xmm2, %xmm5, %xmm5
vpor %xmm4, %xmm3, %xmm4
addl $-2, %ecx
jne chacha_blocks_avx_5
chacha_blocks_avx_6:
vmovdqu 624(%esp), %xmm3
vpaddd 224(%esp), %xmm3, %xmm3
vmovdqu %xmm5, 592(%esp)
vmovdqu %xmm4, 384(%esp)
vmovdqu 640(%esp), %xmm2
vmovdqu 608(%esp), %xmm5
vmovdqu 576(%esp), %xmm4
vmovdqu %xmm3, 400(%esp)
vpaddd 272(%esp), %xmm5, %xmm5
vpaddd 288(%esp), %xmm2, %xmm2
vpaddd 304(%esp), %xmm4, %xmm3
testl %eax, %eax
jne chacha_blocks_avx_7
vmovdqu %xmm0, (%esp)
vmovdqu 400(%esp), %xmm0
vpunpckldq %xmm0, %xmm5, %xmm7
vpunpckldq %xmm3, %xmm2, %xmm4
vmovdqu %xmm6, 16(%esp)
vpunpcklqdq %xmm4, %xmm7, %xmm6
vpunpckhqdq %xmm4, %xmm7, %xmm4
vpunpckhdq %xmm0, %xmm5, %xmm5
vpunpckhdq %xmm3, %xmm2, %xmm2
vpunpcklqdq %xmm2, %xmm5, %xmm3
vpunpckhqdq %xmm2, %xmm5, %xmm5
vmovdqu %xmm6, (%edx)
vmovdqu %xmm4, 64(%edx)
vmovdqu %xmm3, 128(%edx)
vmovdqu %xmm5, 192(%edx)
vmovdqu 544(%esp), %xmm0
vmovdqu 384(%esp), %xmm2
vmovdqu 560(%esp), %xmm4
vmovdqu 592(%esp), %xmm6
vpaddd 336(%esp), %xmm0, %xmm7
vpaddd 240(%esp), %xmm2, %xmm5
vpaddd 320(%esp), %xmm4, %xmm3
vpaddd 208(%esp), %xmm6, %xmm0
vpunpckldq %xmm3, %xmm5, %xmm2
vpunpckldq %xmm0, %xmm7, %xmm4
vpunpckhdq %xmm3, %xmm5, %xmm3
vpunpckhdq %xmm0, %xmm7, %xmm7
vpunpcklqdq %xmm4, %xmm2, %xmm6
vpunpckhqdq %xmm4, %xmm2, %xmm4
vpunpcklqdq %xmm7, %xmm3, %xmm5
vpunpckhqdq %xmm7, %xmm3, %xmm3
vpaddd 192(%esp), %xmm1, %xmm2
vmovdqu (%esp), %xmm1
vmovdqu %xmm4, 80(%edx)
vmovdqu %xmm3, 208(%edx)
vmovdqu %xmm5, 144(%edx)
vmovdqu %xmm6, 16(%edx)
vmovdqu 528(%esp), %xmm3
vmovdqu 512(%esp), %xmm4
vpaddd 176(%esp), %xmm1, %xmm5
vpaddd 160(%esp), %xmm3, %xmm1
vpaddd 144(%esp), %xmm4, %xmm7
vpunpckldq %xmm5, %xmm2, %xmm0
vpunpckldq %xmm7, %xmm1, %xmm6
vpunpckhdq %xmm5, %xmm2, %xmm5
vpunpckhdq %xmm7, %xmm1, %xmm1
vpunpcklqdq %xmm6, %xmm0, %xmm3
vpunpcklqdq %xmm1, %xmm5, %xmm2
vmovdqu %xmm3, 32(%edx)
vmovdqu %xmm2, 160(%edx)
vpunpckhqdq %xmm1, %xmm5, %xmm7
vmovdqu 464(%esp), %xmm3
vmovdqu 16(%esp), %xmm1
vmovdqu 480(%esp), %xmm5
vmovdqu 496(%esp), %xmm2
vpaddd 368(%esp), %xmm3, %xmm4
vpaddd 128(%esp), %xmm5, %xmm5
vpaddd 256(%esp), %xmm2, %xmm2
vpunpckhqdq %xmm6, %xmm0, %xmm6
vpaddd 352(%esp), %xmm1, %xmm0
vmovdqu %xmm6, 96(%edx)
vmovdqu %xmm7, 224(%edx)
vpunpckldq %xmm0, %xmm4, %xmm6
vpunpckldq %xmm2, %xmm5, %xmm7
vpunpckhdq %xmm0, %xmm4, %xmm0
vpunpckhdq %xmm2, %xmm5, %xmm4
vpunpcklqdq %xmm7, %xmm6, %xmm3
vpunpckhqdq %xmm7, %xmm6, %xmm1
vpunpcklqdq %xmm4, %xmm0, %xmm2
vpunpckhqdq %xmm4, %xmm0, %xmm0
vmovdqu %xmm3, 48(%edx)
vmovdqu %xmm1, 112(%edx)
vmovdqu %xmm2, 176(%edx)
vmovdqu %xmm0, 240(%edx)
jmp chacha_blocks_avx_8
chacha_blocks_avx_7:
vmovdqu 400(%esp), %xmm7
vpunpckldq %xmm7, %xmm5, %xmm4
vpunpckhdq %xmm7, %xmm5, %xmm7
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm3, %xmm2, %xmm3
vpunpcklqdq %xmm5, %xmm4, %xmm2
vpunpckhqdq %xmm5, %xmm4, %xmm4
vpxor 64(%eax), %xmm4, %xmm5
vpunpcklqdq %xmm3, %xmm7, %xmm4
vpunpckhqdq %xmm3, %xmm7, %xmm3
vpxor 128(%eax), %xmm4, %xmm4
vpxor 192(%eax), %xmm3, %xmm7
vpxor (%eax), %xmm2, %xmm2
vmovdqu %xmm4, 128(%edx)
vmovdqu %xmm2, (%edx)
vmovdqu %xmm5, 64(%edx)
vmovdqu %xmm7, 192(%edx)
vmovdqu 384(%esp), %xmm4
vpaddd 240(%esp), %xmm4, %xmm3
vmovdqu 560(%esp), %xmm2
vmovdqu 544(%esp), %xmm5
vmovdqu 592(%esp), %xmm4
vpaddd 320(%esp), %xmm2, %xmm2
vpaddd 336(%esp), %xmm5, %xmm7
vpaddd 208(%esp), %xmm4, %xmm4
vpunpckldq %xmm2, %xmm3, %xmm5
vpunpckhdq %xmm2, %xmm3, %xmm2
vpunpckldq %xmm4, %xmm7, %xmm3
vpunpckhdq %xmm4, %xmm7, %xmm4
vpunpcklqdq %xmm3, %xmm5, %xmm7
vpunpckhqdq %xmm3, %xmm5, %xmm5
vpxor 80(%eax), %xmm5, %xmm3
vpunpcklqdq %xmm4, %xmm2, %xmm5
vpunpckhqdq %xmm4, %xmm2, %xmm2
vpxor 16(%eax), %xmm7, %xmm7
vpxor 144(%eax), %xmm5, %xmm5
vpxor 208(%eax), %xmm2, %xmm4
vmovdqu %xmm7, 16(%edx)
vmovdqu %xmm5, 144(%edx)
vmovdqu %xmm3, 80(%edx)
vmovdqu %xmm4, 208(%edx)
vpaddd 176(%esp), %xmm0, %xmm7
vpaddd 192(%esp), %xmm1, %xmm5
vmovdqu 528(%esp), %xmm0
vmovdqu 512(%esp), %xmm1
vpaddd 160(%esp), %xmm0, %xmm3
vpaddd 144(%esp), %xmm1, %xmm0
vpunpckldq %xmm7, %xmm5, %xmm1
vpunpckldq %xmm0, %xmm3, %xmm2
vpunpckhdq %xmm7, %xmm5, %xmm7
vpunpckhdq %xmm0, %xmm3, %xmm4
vpunpcklqdq %xmm2, %xmm1, %xmm3
vpunpckhqdq %xmm2, %xmm1, %xmm1
vpunpcklqdq %xmm4, %xmm7, %xmm2
vpunpckhqdq %xmm4, %xmm7, %xmm7
vpxor 32(%eax), %xmm3, %xmm0
vpxor 96(%eax), %xmm1, %xmm1
vpxor 160(%eax), %xmm2, %xmm3
vpxor 224(%eax), %xmm7, %xmm4
vmovdqu %xmm0, 32(%edx)
vmovdqu %xmm1, 96(%edx)
vmovdqu %xmm3, 160(%edx)
vmovdqu %xmm4, 224(%edx)
vpaddd 352(%esp), %xmm6, %xmm0
vmovdqu 480(%esp), %xmm6
vpaddd 128(%esp), %xmm6, %xmm2
vmovdqu 464(%esp), %xmm5
vmovdqu 496(%esp), %xmm6
vpaddd 368(%esp), %xmm5, %xmm1
vpaddd 256(%esp), %xmm6, %xmm3
vpunpckldq %xmm0, %xmm1, %xmm7
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm0, %xmm1, %xmm1
vpunpckhdq %xmm3, %xmm2, %xmm0
vpunpcklqdq %xmm5, %xmm7, %xmm4
vpunpckhqdq %xmm5, %xmm7, %xmm7
vpunpcklqdq %xmm0, %xmm1, %xmm2
vpunpckhqdq %xmm0, %xmm1, %xmm0
vpxor 48(%eax), %xmm4, %xmm6
vpxor 112(%eax), %xmm7, %xmm3
vpxor 176(%eax), %xmm2, %xmm4
vpxor 240(%eax), %xmm0, %xmm1
addl $256, %eax
vmovdqu %xmm6, 48(%edx)
vmovdqu %xmm3, 112(%edx)
vmovdqu %xmm4, 176(%edx)
vmovdqu %xmm1, 240(%edx)
chacha_blocks_avx_8:
movl 420(%esp), %ecx
addl $256, %edx
addl $-256, %ecx
movl %ecx, 420(%esp)
cmpl $256, %ecx
jae chacha_blocks_avx_4
chacha_blocks_avx_9:
movl 8(%ebp), %ecx
movl %edi, 32(%ecx)
movl %esi, 36(%ecx)
movl 420(%esp), %ebx
vmovdqu 32(%ecx), %xmm0
chacha_blocks_avx_10:
cmpl $128, %ebx
jb chacha_blocks_avx_16
chacha_blocks_avx_11:
vmovdqu 64(%esp), %xmm3
vmovdqa %xmm0, %xmm1
vmovdqu 80(%esp), %xmm4
vmovdqu 48(%esp), %xmm6
vpaddq 96(%esp), %xmm0, %xmm2
vmovdqu %xmm3, 32(%esp)
vmovdqu %xmm4, 16(%esp)
vmovdqu %xmm6, 128(%esp)
vmovdqu %xmm6, 160(%esp)
vmovdqu %xmm2, (%esp)
vmovdqu %xmm2, 144(%esp)
movl 424(%esp), %esi
vmovdqu 16(%esp), %xmm5
vmovdqu 32(%esp), %xmm6
vmovdqu %xmm0, 112(%esp)
chacha_blocks_avx_12:
vpaddd 160(%esp), %xmm3, %xmm0
vpaddd 128(%esp), %xmm6, %xmm2
vpxor %xmm0, %xmm1, %xmm1
vmovdqu 448(%esp), %xmm7
vmovdqu %xmm2, 176(%esp)
vpshufb %xmm7, %xmm1, %xmm1
vpxor 144(%esp), %xmm2, %xmm2
vpaddd %xmm1, %xmm4, %xmm4
vpshufb %xmm7, %xmm2, %xmm2
vpaddd %xmm2, %xmm5, %xmm5
vpxor %xmm4, %xmm3, %xmm3
vpxor %xmm5, %xmm6, %xmm7
vpsrld $20, %xmm3, %xmm6
vpslld $12, %xmm3, %xmm3
vpor %xmm3, %xmm6, %xmm6
vpsrld $20, %xmm7, %xmm3
vpslld $12, %xmm7, %xmm7
vpaddd %xmm6, %xmm0, %xmm0
vpor %xmm7, %xmm3, %xmm7
vpxor %xmm0, %xmm1, %xmm1
vmovdqu %xmm0, 192(%esp)
vpaddd 176(%esp), %xmm7, %xmm3
vmovdqu 432(%esp), %xmm0
vpxor %xmm3, %xmm2, %xmm2
vpshufb %xmm0, %xmm1, %xmm1
vpshufb %xmm0, %xmm2, %xmm0
vpaddd %xmm1, %xmm4, %xmm4
vpaddd %xmm0, %xmm5, %xmm5
vpxor %xmm4, %xmm6, %xmm6
vpxor %xmm5, %xmm7, %xmm7
vpsrld $25, %xmm6, %xmm2
vpslld $7, %xmm6, %xmm6
vpor %xmm6, %xmm2, %xmm2
vpsrld $25, %xmm7, %xmm6
vpslld $7, %xmm7, %xmm7
vpor %xmm7, %xmm6, %xmm6
vpshufd $147, 192(%esp), %xmm7
vpshufd $147, %xmm3, %xmm3
vpaddd %xmm2, %xmm7, %xmm7
vpshufd $78, %xmm1, %xmm1
vpaddd %xmm6, %xmm3, %xmm3
vmovdqu %xmm7, 208(%esp)
vpxor %xmm7, %xmm1, %xmm7
vmovdqu 448(%esp), %xmm1
vpshufd $78, %xmm0, %xmm0
vpshufb %xmm1, %xmm7, %xmm7
vpxor %xmm3, %xmm0, %xmm0
vpshufb %xmm1, %xmm0, %xmm0
vpshufd $57, %xmm4, %xmm4
vpshufd $57, %xmm5, %xmm5
vpaddd %xmm7, %xmm4, %xmm1
vpaddd %xmm0, %xmm5, %xmm5
vpxor %xmm1, %xmm2, %xmm4
vpxor %xmm5, %xmm6, %xmm2
vpsrld $20, %xmm4, %xmm6
vpslld $12, %xmm4, %xmm4
vpor %xmm4, %xmm6, %xmm4
vpsrld $20, %xmm2, %xmm6
vpslld $12, %xmm2, %xmm2
vpor %xmm2, %xmm6, %xmm2
vpaddd 208(%esp), %xmm4, %xmm6
vpaddd %xmm2, %xmm3, %xmm3
vmovdqu %xmm2, 224(%esp)
vpxor %xmm6, %xmm7, %xmm7
vmovdqu 432(%esp), %xmm2
vpxor %xmm3, %xmm0, %xmm0
vpshufb %xmm2, %xmm7, %xmm7
vpshufb %xmm2, %xmm0, %xmm0
vpshufd $57, %xmm3, %xmm3
vpaddd %xmm0, %xmm5, %xmm5
vmovdqu %xmm3, 128(%esp)
vpaddd %xmm7, %xmm1, %xmm3
vpshufd $78, %xmm0, %xmm0
vpxor %xmm3, %xmm4, %xmm2
vmovdqu %xmm0, 144(%esp)
vpxor 224(%esp), %xmm5, %xmm0
vpshufd $57, %xmm6, %xmm6
vmovdqu %xmm6, 160(%esp)
vpsrld $25, %xmm2, %xmm6
vpshufd $78, %xmm7, %xmm1
vpslld $7, %xmm2, %xmm7
vpsrld $25, %xmm0, %xmm2
vpslld $7, %xmm0, %xmm0
vpshufd $147, %xmm3, %xmm4
vpor %xmm7, %xmm6, %xmm3
vpshufd $147, %xmm5, %xmm5
vpor %xmm0, %xmm2, %xmm6
addl $-2, %esi
jne chacha_blocks_avx_12
chacha_blocks_avx_13:
vmovdqu 64(%esp), %xmm2
vmovdqu %xmm5, 16(%esp)
vpaddd %xmm3, %xmm2, %xmm7
vmovdqu %xmm6, 32(%esp)
vmovdqu 112(%esp), %xmm0
vmovdqu 48(%esp), %xmm5
vpaddd %xmm1, %xmm0, %xmm1
vmovdqu 160(%esp), %xmm6
vmovdqu 80(%esp), %xmm3
vpaddd %xmm6, %xmm5, %xmm6
vpaddd 128(%esp), %xmm5, %xmm0
vpaddd %xmm4, %xmm3, %xmm4
vpaddd 32(%esp), %xmm2, %xmm5
vpaddd 16(%esp), %xmm3, %xmm2
vmovdqu (%esp), %xmm3
vpaddd 144(%esp), %xmm3, %xmm3
testl %eax, %eax
je chacha_blocks_avx_15
chacha_blocks_avx_14:
vpxor (%eax), %xmm6, %xmm6
vpxor 16(%eax), %xmm7, %xmm7
vpxor 32(%eax), %xmm4, %xmm4
vpxor 48(%eax), %xmm1, %xmm1
vpxor 64(%eax), %xmm0, %xmm0
vpxor 80(%eax), %xmm5, %xmm5
vpxor 96(%eax), %xmm2, %xmm2
vpxor 112(%eax), %xmm3, %xmm3
addl $128, %eax
chacha_blocks_avx_15:
vmovdqu %xmm0, 64(%edx)
vmovdqu %xmm6, (%edx)
vmovdqu %xmm7, 16(%edx)
vmovdqu %xmm4, 32(%edx)
vmovdqu %xmm1, 48(%edx)
vmovdqu %xmm5, 80(%edx)
vmovdqu %xmm2, 96(%edx)
vmovdqu %xmm3, 112(%edx)
addl $-128, %ebx
addl $128, %edx
vmovdqu (%esp), %xmm0
vpaddq 96(%esp), %xmm0, %xmm0
chacha_blocks_avx_16:
movl %ebx, %edi
testl %ebx, %ebx
jne chacha_blocks_avx_18
chacha_blocks_avx_17:
vmovdqu %xmm0, 32(%ecx)
addl $1268, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx_18:
movl %edi, 20(%esp)
xorl %esi, %esi
movl %ebx, 420(%esp)
vmovdqu 80(%esp), %xmm7
vmovdqu 64(%esp), %xmm1
vmovdqu 48(%esp), %xmm6
jmp chacha_blocks_avx_19
chacha_blocks_avx_35:
movl %ecx, 420(%esp)
addl $64, %edx
chacha_blocks_avx_19:
incl %esi
movl %esi, %ecx
shll $6, %ecx
negl %ecx
addl 20(%esp), %ecx
lea 64(%ecx), %ebx
cmpl $64, %ebx
jae chacha_blocks_avx_30
chacha_blocks_avx_20:
testl %eax, %eax
je chacha_blocks_avx_29
chacha_blocks_avx_21:
testl %ebx, %ebx
je chacha_blocks_avx_28
chacha_blocks_avx_22:
movl %ebx, %edi
shrl $1, %edi
movl %edi, 12(%esp)
testl %edi, %edi
jbe chacha_blocks_avx_37
chacha_blocks_avx_23:
movl %esi, 8(%esp)
xorl %edi, %edi
movl %ecx, 4(%esp)
movl %edx, 16(%esp)
movl 12(%esp), %esi
chacha_blocks_avx_24:
movzbl (%eax,%edi,2), %edx
movb %dl, 128(%esp,%edi,2)
movzbl 1(%eax,%edi,2), %ecx
movb %cl, 129(%esp,%edi,2)
incl %edi
cmpl %esi, %edi
jb chacha_blocks_avx_24
chacha_blocks_avx_25:
movl 4(%esp), %ecx
lea 1(%edi,%edi), %edi
movl 8(%esp), %esi
movl 16(%esp), %edx
movl %edi, (%esp)
chacha_blocks_avx_26:
lea -1(%edi), %edi
cmpl %ebx, %edi
jae chacha_blocks_avx_28
chacha_blocks_avx_27:
movzbl (%edi,%eax), %eax
movl (%esp), %edi
movb %al, 127(%esp,%edi)
chacha_blocks_avx_28:
lea 128(%esp), %eax
chacha_blocks_avx_29:
movl %edx, 416(%esp)
lea 128(%esp), %edx
chacha_blocks_avx_30:
vmovdqu %xmm0, 112(%esp)
vmovdqa %xmm6, %xmm2
movl %edx, 16(%esp)
xorl %edi, %edi
movl %eax, 24(%esp)
vmovdqa %xmm1, %xmm3
vmovdqu 448(%esp), %xmm1
vmovdqa %xmm7, %xmm4
movl 424(%esp), %edx
vmovdqa %xmm0, %xmm5
vmovdqu 432(%esp), %xmm0
chacha_blocks_avx_31:
vpaddd %xmm3, %xmm2, %xmm6
incl %edi
vpxor %xmm6, %xmm5, %xmm2
vpshufb %xmm1, %xmm2, %xmm5
vpaddd %xmm5, %xmm4, %xmm2
lea (%edi,%edi), %eax
vpxor %xmm2, %xmm3, %xmm4
vpsrld $20, %xmm4, %xmm3
vpslld $12, %xmm4, %xmm7
vpor %xmm7, %xmm3, %xmm7
vpaddd %xmm7, %xmm6, %xmm3
vpxor %xmm3, %xmm5, %xmm5
vpshufb %xmm0, %xmm5, %xmm4
vpaddd %xmm4, %xmm2, %xmm6
vpxor %xmm6, %xmm7, %xmm2
vpsrld $25, %xmm2, %xmm5
vpslld $7, %xmm2, %xmm7
vpshufd $147, %xmm3, %xmm3
vpor %xmm7, %xmm5, %xmm5
vpshufd $78, %xmm4, %xmm4
vpaddd %xmm5, %xmm3, %xmm2
vpxor %xmm2, %xmm4, %xmm4
vpshufb %xmm1, %xmm4, %xmm7
vpshufd $57, %xmm6, %xmm6
vpaddd %xmm7, %xmm6, %xmm3
vpxor %xmm3, %xmm5, %xmm4
vpsrld $20, %xmm4, %xmm5
vpslld $12, %xmm4, %xmm6
vpor %xmm6, %xmm5, %xmm4
vpaddd %xmm4, %xmm2, %xmm5
vpxor %xmm5, %xmm7, %xmm2
vpshufb %xmm0, %xmm2, %xmm7
vpaddd %xmm7, %xmm3, %xmm3
vpxor %xmm3, %xmm4, %xmm6
vpshufd $57, %xmm5, %xmm2
vpshufd $78, %xmm7, %xmm5
vpslld $7, %xmm6, %xmm7
vpshufd $147, %xmm3, %xmm4
vpsrld $25, %xmm6, %xmm3
vpor %xmm7, %xmm3, %xmm3
cmpl %edx, %eax
jne chacha_blocks_avx_31
chacha_blocks_avx_32:
vmovdqu 80(%esp), %xmm7
vmovdqu 64(%esp), %xmm1
vpaddd %xmm7, %xmm4, %xmm4
vmovdqu 48(%esp), %xmm6
vpaddd %xmm1, %xmm3, %xmm3
vmovdqu 112(%esp), %xmm0
vpaddd %xmm6, %xmm2, %xmm2
movl 24(%esp), %eax
vpaddd %xmm0, %xmm5, %xmm5
movl 16(%esp), %edx
testl %eax, %eax
je chacha_blocks_avx_34
chacha_blocks_avx_33:
vpxor (%eax), %xmm2, %xmm2
vpxor 16(%eax), %xmm3, %xmm3
vpxor 32(%eax), %xmm4, %xmm4
vpxor 48(%eax), %xmm5, %xmm5
addl $64, %eax
chacha_blocks_avx_34:
vmovdqu %xmm2, (%edx)
vmovdqu %xmm3, 16(%edx)
vmovdqu %xmm4, 32(%edx)
vmovdqu %xmm5, 48(%edx)
vpaddq 96(%esp), %xmm0, %xmm0
cmpl $64, %ebx
jbe chacha_blocks_avx_38
jmp chacha_blocks_avx_35
chacha_blocks_avx_36:
addl $1268, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx_37:
movl $1, %edi
movl %edi, (%esp)
jmp chacha_blocks_avx_26
chacha_blocks_avx_38:
movl 420(%esp), %ebx
movl 8(%ebp), %ecx
cmpl $64, %ebx
jae chacha_blocks_avx_17
chacha_blocks_avx_39:
testl %ebx, %ebx
jbe chacha_blocks_avx_17
chacha_blocks_avx_40:
movl 416(%esp), %edi
xorl %esi, %esi
chacha_blocks_avx_41:
movzbl (%esi,%edx), %eax
movb %al, (%esi,%edi)
incl %esi
cmpl %ebx, %esi
jb chacha_blocks_avx_41
jmp chacha_blocks_avx_17
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

INCLUDE_VAR_FILE "chacha/chacha_constants_x86.inc", chacha_constants

