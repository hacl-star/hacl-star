SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_xop
chacha_blocks_xop_local:
pushl %ebp
movl %esp, %ebp
andl $~63, %esp
sub $704, %esp
movl %ebx, 68(%esp)
movl %esi, 72(%esp)
movl %edi, 76(%esp)
movl 8(%ebp), %ecx
movl %ecx, 84(%esp)
movl 12(%ebp), %esi
movl 16(%ebp), %edx
movl 20(%ebp), %eax
LOAD_VAR_PIC chacha_constants, %ebx
vmovdqa 0(%ebx), %xmm0
vmovdqu 0(%ecx), %xmm1
vmovdqu 16(%ecx), %xmm2
vmovdqu 32(%ecx), %xmm3
vmovdqa %xmm0, 0(%esp)
vmovdqa %xmm1, 16(%esp)
vmovdqa %xmm2, 32(%esp)
vmovdqa %xmm3, 48(%esp)
movl 48(%ecx), %ecx
movl %ecx, 88(%esp)
cmpl $128, %eax
jb chacha_blocks_xop_bytesbetween0and127
cmpl $256, %eax
jb chacha_blocks_xop_bytesatleast128
vpshufd $0x00, %xmm0, %xmm4
vpshufd $0x55, %xmm0, %xmm5
vpshufd $0xaa, %xmm0, %xmm6
vpshufd $0xff, %xmm0, %xmm0
vmovdqa %xmm4, 128(%esp)
vmovdqa %xmm5, 192(%esp)
vmovdqa %xmm6, 288(%esp)
vmovdqa %xmm0, 304(%esp)
vpshufd $0x00, %xmm1, %xmm0
vpshufd $0x55, %xmm1, %xmm4
vpshufd $0xaa, %xmm1, %xmm5
vpshufd $0xff, %xmm1, %xmm1
vmovdqa %xmm0, 144(%esp)
vmovdqa %xmm4, 208(%esp)
vmovdqa %xmm5, 256(%esp)
vmovdqa %xmm1, 272(%esp)
vpshufd $0x00, %xmm2, %xmm0
vpshufd $0x55, %xmm2, %xmm1
vpshufd $0xaa, %xmm2, %xmm4
vpshufd $0xff, %xmm2, %xmm2
vmovdqa %xmm0, 160(%esp)
vmovdqa %xmm1, 224(%esp)
vmovdqa %xmm4, 352(%esp)
vmovdqa %xmm2, 368(%esp)
vpshufd $0xaa, %xmm3, %xmm0
vpshufd $0xff, %xmm3, %xmm1
vmovdqa %xmm0, 320(%esp)
vmovdqa %xmm1, 336(%esp)
jmp chacha_blocks_xop_bytesatleast256
.p2align 6, ,63
chacha_blocks_xop_bytesatleast256:
movl 48(%esp), %ecx
movl 4+48(%esp), %ebx
movl %ecx, 176(%esp)
movl %ebx, 240(%esp)
addl $1, %ecx
adcl $0, %ebx
movl %ecx, 4+176(%esp)
movl %ebx, 4+240(%esp)
addl $1, %ecx
adcl $0, %ebx
movl %ecx, 8+176(%esp)
movl %ebx, 8+240(%esp)
addl $1, %ecx
adcl $0, %ebx
movl %ecx, 12+176(%esp)
movl %ebx, 12+240(%esp)
addl $1, %ecx
adcl $0, %ebx
movl %ecx, 48(%esp)
movl %ebx, 4+48(%esp)
movl %eax, 92(%esp)
movl 88(%esp), %eax
vmovdqa 256(%esp), %xmm0
vmovdqa 272(%esp), %xmm1
vmovdqa 288(%esp), %xmm2
vmovdqa 304(%esp), %xmm3
vmovdqa 320(%esp), %xmm4
vmovdqa 336(%esp), %xmm5
vmovdqa 352(%esp), %xmm6
vmovdqa 368(%esp), %xmm7
vmovdqa %xmm0, 576(%esp)
vmovdqa %xmm1, 592(%esp)
vmovdqa %xmm2, 608(%esp)
vmovdqa %xmm3, 624(%esp)
vmovdqa %xmm4, 640(%esp)
vmovdqa %xmm5, 656(%esp)
vmovdqa %xmm6, 672(%esp)
vmovdqa %xmm7, 688(%esp)
vmovdqa 128(%esp), %xmm0
vmovdqa 144(%esp), %xmm1
vmovdqa 160(%esp), %xmm2
vmovdqa 176(%esp), %xmm3
vmovdqa 192(%esp), %xmm4
vmovdqa 208(%esp), %xmm5
vmovdqa 224(%esp), %xmm6
vmovdqa 240(%esp), %xmm7
chacha_blocks_xop_mainloop1:
vpaddd %xmm1, %xmm0, %xmm0
vpxor %xmm0, %xmm3, %xmm3
vprotd $16, %xmm3, %xmm3
vpaddd %xmm5, %xmm4, %xmm4
vpxor %xmm4, %xmm7, %xmm7
vprotd $16, %xmm7, %xmm7
vpaddd %xmm3, %xmm2, %xmm2
vpaddd %xmm7, %xmm6, %xmm6
vpxor %xmm2, %xmm1, %xmm1
vpxor %xmm6, %xmm5, %xmm5
vprotd $12, %xmm1, %xmm1
vpaddd %xmm1, %xmm0, %xmm0
vprotd $12, %xmm5, %xmm5
vpaddd %xmm5, %xmm4, %xmm4
vpxor %xmm0, %xmm3, %xmm3
vpxor %xmm4, %xmm7, %xmm7
vprotd $8, %xmm3, %xmm3
vprotd $8, %xmm7, %xmm7
vpaddd %xmm3, %xmm2, %xmm2
vpaddd %xmm7, %xmm6, %xmm6
vpxor %xmm2, %xmm1, %xmm1
vpxor %xmm6, %xmm5, %xmm5
vprotd $7, %xmm1, %xmm1
vprotd $7, %xmm5, %xmm5
vmovdqa %xmm1, 464(%esp)
vmovdqa 576(%esp), %xmm1
vmovdqa %xmm5, 528(%esp)
vmovdqa 592(%esp), %xmm5
vmovdqa %xmm0, 448(%esp)
vmovdqa %xmm4, 512(%esp)
vmovdqa %xmm2, 480(%esp)
vmovdqa %xmm6, 544(%esp)
vmovdqa %xmm3, 496(%esp)
vmovdqa %xmm7, 560(%esp)
vpaddd 608(%esp), %xmm1, %xmm0
vpaddd 624(%esp), %xmm5, %xmm4
vpxor 640(%esp), %xmm0, %xmm3
vpxor 656(%esp), %xmm4, %xmm7
vprotd $16, %xmm3, %xmm3
vpaddd 672(%esp), %xmm3, %xmm2
vprotd $16, %xmm7, %xmm7
vpaddd 688(%esp), %xmm7, %xmm6
vpxor %xmm2, %xmm1, %xmm1
vpxor %xmm6, %xmm5, %xmm5
vprotd $12, %xmm1, %xmm1
vpaddd %xmm1, %xmm0, %xmm0
vprotd $12, %xmm5, %xmm5
vpaddd %xmm5, %xmm4, %xmm4
vpxor %xmm0, %xmm3, %xmm3
vpxor %xmm4, %xmm7, %xmm7
vprotd $8, %xmm3, %xmm3
vpaddd %xmm3, %xmm2, %xmm2
vprotd $8, %xmm7, %xmm7
vpaddd %xmm7, %xmm6, %xmm6
vpxor %xmm2, %xmm1, %xmm1
vpxor %xmm6, %xmm5, %xmm5
vprotd $7, %xmm1, %xmm1
vprotd $7, %xmm5, %xmm5
vmovdqa %xmm3, 640(%esp)
vmovdqa %xmm4, 624(%esp)
vmovdqa %xmm0, 608(%esp)
vmovdqa %xmm5, 592(%esp)
vmovdqa 528(%esp), %xmm5
vpaddd 448(%esp), %xmm5, %xmm4
vpaddd 512(%esp), %xmm1, %xmm0
vpxor %xmm7, %xmm4, %xmm7
vpxor 496(%esp), %xmm0, %xmm3
vprotd $16, %xmm7, %xmm7
vpaddd %xmm7, %xmm2, %xmm2
vprotd $16, %xmm3, %xmm3
vpaddd %xmm3, %xmm6, %xmm6
vpxor %xmm2, %xmm5, %xmm5
vpxor %xmm6, %xmm1, %xmm1
vprotd $12, %xmm5, %xmm5
vpaddd %xmm5, %xmm4, %xmm4
vprotd $12, %xmm1, %xmm1
vpaddd %xmm1, %xmm0, %xmm0
vpxor %xmm4, %xmm7, %xmm7
vpxor %xmm0, %xmm3, %xmm3
vprotd $8, %xmm7, %xmm7
vpaddd %xmm7, %xmm2, %xmm2
vprotd $8, %xmm3, %xmm3
vpaddd %xmm3, %xmm6, %xmm6
vpxor %xmm2, %xmm5, %xmm5
vpxor %xmm6, %xmm1, %xmm1
vprotd $7, %xmm5, %xmm5
vprotd $7, %xmm1, %xmm1
vmovdqa %xmm4, 448(%esp)
vmovdqa %xmm3, 496(%esp)
vmovdqa %xmm0, 512(%esp)
vmovdqa %xmm5, 528(%esp)
vmovdqa %xmm1, 576(%esp)
vmovdqa %xmm7, 656(%esp)
vmovdqa %xmm2, 672(%esp)
vmovdqa %xmm6, 688(%esp)
vmovdqa 592(%esp), %xmm1
vmovdqa 464(%esp), %xmm5
vpaddd 608(%esp), %xmm1, %xmm0
vpaddd 624(%esp), %xmm5, %xmm4
vpxor 560(%esp), %xmm0, %xmm3
vpxor 640(%esp), %xmm4, %xmm7
vprotd $16, %xmm3, %xmm3
vpaddd 480(%esp), %xmm3, %xmm2
vprotd $16, %xmm7, %xmm7
vpaddd 544(%esp), %xmm7, %xmm6
vpxor %xmm2, %xmm1, %xmm1
vpxor %xmm6, %xmm5, %xmm5
vprotd $12, %xmm1, %xmm1
vpaddd %xmm1, %xmm0, %xmm0
vprotd $12, %xmm5, %xmm5
vpaddd %xmm5, %xmm4, %xmm4
vpxor %xmm0, %xmm3, %xmm3
vpxor %xmm4, %xmm7, %xmm7
vprotd $8, %xmm3, %xmm3
vpaddd %xmm3, %xmm2, %xmm2
vprotd $8, %xmm7, %xmm7
vpaddd %xmm7, %xmm6, %xmm6
vpxor %xmm2, %xmm1, %xmm1
vpxor %xmm6, %xmm5, %xmm5
vprotd $7, %xmm1, %xmm1
vprotd $7, %xmm5, %xmm5
vmovdqa %xmm7, 640(%esp)
vmovdqa %xmm4, 624(%esp)
vmovdqa %xmm0, 608(%esp)
vmovdqa %xmm1, 592(%esp)
vmovdqa %xmm3, %xmm7
vmovdqa %xmm5, %xmm1
vmovdqa 448(%esp), %xmm0
vmovdqa 496(%esp), %xmm3
vmovdqa 512(%esp), %xmm4
vmovdqa 528(%esp), %xmm5
subl $2, %eax
ja chacha_blocks_xop_mainloop1
vmovdqa %xmm2, 480(%esp)
vmovdqa %xmm6, 544(%esp)
vmovdqa %xmm1, 464(%esp)
vmovdqa %xmm7, 560(%esp)
cmpl $0, %esi
jbe chacha_blocks_xop_noinput1
vmovdqa 448(%esp), %xmm0
vmovdqa 512(%esp), %xmm1
vmovdqa 608(%esp), %xmm2
vmovdqa 624(%esp), %xmm3
vpaddd 128(%esp), %xmm0, %xmm0
vpaddd 192(%esp), %xmm1, %xmm1
vpaddd 288(%esp), %xmm2, %xmm2
vpaddd 304(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vpxor 0(%esi), %xmm0, %xmm0
vpxor 64(%esi), %xmm1, %xmm1
vpxor 128(%esi), %xmm2, %xmm2
vpxor 192(%esi), %xmm3, %xmm3
vmovdqu %xmm0, 0(%edx)
vmovdqu %xmm1, 64(%edx)
vmovdqu %xmm2, 128(%edx)
vmovdqu %xmm3, 192(%edx)
vmovdqa 464(%esp), %xmm0
vmovdqa 528(%esp), %xmm1
vmovdqa 576(%esp), %xmm2
vmovdqa 592(%esp), %xmm3
vpaddd 144(%esp), %xmm0, %xmm0
vpaddd 208(%esp), %xmm1, %xmm1
vpaddd 256(%esp), %xmm2, %xmm2
vpaddd 272(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vpxor 16+0(%esi), %xmm0, %xmm0
vpxor 16+64(%esi), %xmm1, %xmm1
vpxor 16+128(%esi), %xmm2, %xmm2
vpxor 16+192(%esi), %xmm3, %xmm3
vmovdqu %xmm0, 16+0(%edx)
vmovdqu %xmm1, 16+64(%edx)
vmovdqu %xmm2, 16+128(%edx)
vmovdqu %xmm3, 16+192(%edx)
vmovdqa 480(%esp), %xmm0
vmovdqa 544(%esp), %xmm1
vmovdqa 672(%esp), %xmm2
vmovdqa 688(%esp), %xmm3
vpaddd 160(%esp), %xmm0, %xmm0
vpaddd 224(%esp), %xmm1, %xmm1
vpaddd 352(%esp), %xmm2, %xmm2
vpaddd 368(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vpxor 32+0(%esi), %xmm0, %xmm0
vpxor 32+64(%esi), %xmm1, %xmm1
vpxor 32+128(%esi), %xmm2, %xmm2
vpxor 32+192(%esi), %xmm3, %xmm3
vmovdqu %xmm0, 32+0(%edx)
vmovdqu %xmm1, 32+64(%edx)
vmovdqu %xmm2, 32+128(%edx)
vmovdqu %xmm3, 32+192(%edx)
vmovdqa 496(%esp), %xmm0
vmovdqa 560(%esp), %xmm1
vmovdqa 640(%esp), %xmm2
vmovdqa 656(%esp), %xmm3
vpaddd 176(%esp), %xmm0, %xmm0
vpaddd 240(%esp), %xmm1, %xmm1
vpaddd 320(%esp), %xmm2, %xmm2
vpaddd 336(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vpxor 48+0(%esi), %xmm0, %xmm0
vpxor 48+64(%esi), %xmm1, %xmm1
vpxor 48+128(%esi), %xmm2, %xmm2
vpxor 48+192(%esi), %xmm3, %xmm3
vmovdqu %xmm0, 48+0(%edx)
vmovdqu %xmm1, 48+64(%edx)
vmovdqu %xmm2, 48+128(%edx)
vmovdqu %xmm3, 48+192(%edx)
addl $256, %esi
jmp chacha_blocks_xop_mainloop1_cont
chacha_blocks_xop_noinput1:
vmovdqa 448(%esp), %xmm0
vmovdqa 512(%esp), %xmm1
vmovdqa 608(%esp), %xmm2
vmovdqa 624(%esp), %xmm3
vpaddd 128(%esp), %xmm0, %xmm0
vpaddd 192(%esp), %xmm1, %xmm1
vpaddd 288(%esp), %xmm2, %xmm2
vpaddd 304(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vmovdqu %xmm0, 0(%edx)
vmovdqu %xmm1, 64(%edx)
vmovdqu %xmm2, 128(%edx)
vmovdqu %xmm3, 192(%edx)
vmovdqa 464(%esp), %xmm0
vmovdqa 528(%esp), %xmm1
vmovdqa 576(%esp), %xmm2
vmovdqa 592(%esp), %xmm3
vpaddd 144(%esp), %xmm0, %xmm0
vpaddd 208(%esp), %xmm1, %xmm1
vpaddd 256(%esp), %xmm2, %xmm2
vpaddd 272(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vmovdqu %xmm0, 16+0(%edx)
vmovdqu %xmm1, 16+64(%edx)
vmovdqu %xmm2, 16+128(%edx)
vmovdqu %xmm3, 16+192(%edx)
vmovdqa 480(%esp), %xmm0
vmovdqa 544(%esp), %xmm1
vmovdqa 672(%esp), %xmm2
vmovdqa 688(%esp), %xmm3
vpaddd 160(%esp), %xmm0, %xmm0
vpaddd 224(%esp), %xmm1, %xmm1
vpaddd 352(%esp), %xmm2, %xmm2
vpaddd 368(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vmovdqu %xmm0, 32+0(%edx)
vmovdqu %xmm1, 32+64(%edx)
vmovdqu %xmm2, 32+128(%edx)
vmovdqu %xmm3, 32+192(%edx)
vmovdqa 496(%esp), %xmm0
vmovdqa 560(%esp), %xmm1
vmovdqa 640(%esp), %xmm2
vmovdqa 656(%esp), %xmm3
vpaddd 176(%esp), %xmm0, %xmm0
vpaddd 240(%esp), %xmm1, %xmm1
vpaddd 320(%esp), %xmm2, %xmm2
vpaddd 336(%esp), %xmm3, %xmm3
vpunpckldq %xmm1, %xmm0, %xmm4
vpunpckldq %xmm3, %xmm2, %xmm5
vpunpckhdq %xmm1, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm2, %xmm7
vpunpcklqdq %xmm5, %xmm4, %xmm0
vpunpckhqdq %xmm5, %xmm4, %xmm1
vpunpcklqdq %xmm7, %xmm6, %xmm2
vpunpckhqdq %xmm7, %xmm6, %xmm3
vmovdqu %xmm0, 48+0(%edx)
vmovdqu %xmm1, 48+64(%edx)
vmovdqu %xmm2, 48+128(%edx)
vmovdqu %xmm3, 48+192(%edx)
chacha_blocks_xop_mainloop1_cont:
movl 92(%esp), %eax
subl $256, %eax
addl $256, %edx
cmpl $256, %eax
jae chacha_blocks_xop_bytesatleast256
cmpl $128, %eax
jb chacha_blocks_xop_bytesbetween0and127
chacha_blocks_xop_bytesatleast128:
movl $1, %ecx
vmovdqa 0(%esp), %xmm0
vmovdqa 16(%esp), %xmm1
vmovdqa 32(%esp), %xmm2
vmovdqa 48(%esp), %xmm3
vmovd %ecx, %xmm7
vmovdqa %xmm0, %xmm4
vmovdqa %xmm1, %xmm5
vmovdqa %xmm2, %xmm6
vpaddq %xmm3, %xmm7, %xmm7
movl %eax, 92(%esp)
movl 88(%esp), %eax
vmovdqa %xmm7, 448(%esp)
chacha_blocks_xop_mainloop2:
vpaddd %xmm0, %xmm1, %xmm0
vpaddd %xmm4, %xmm5, %xmm4
vpxor %xmm3, %xmm0, %xmm3
vpxor %xmm7, %xmm4, %xmm7
vprotd $16, %xmm3, %xmm3
vprotd $16, %xmm7, %xmm7
vpaddd %xmm2, %xmm3, %xmm2
vpaddd %xmm6, %xmm7, %xmm6
vpxor %xmm1, %xmm2, %xmm1
vpxor %xmm5, %xmm6, %xmm5
vprotd $12, %xmm1, %xmm1
vprotd $12, %xmm5, %xmm5
vpaddd %xmm0, %xmm1, %xmm0
vpaddd %xmm4, %xmm5, %xmm4
vpxor %xmm3, %xmm0, %xmm3
vpxor %xmm7, %xmm4, %xmm7
vprotd $8, %xmm3, %xmm3
vprotd $8, %xmm7, %xmm7
vpaddd %xmm2, %xmm3, %xmm2
vpaddd %xmm6, %xmm7, %xmm6
vpshufd $0x93, %xmm0, %xmm0
vpshufd $0x93, %xmm4, %xmm4
vpxor %xmm1, %xmm2, %xmm1
vpxor %xmm5, %xmm6, %xmm5
vprotd $7, %xmm1, %xmm1
vprotd $7, %xmm5, %xmm5
vpshufd $0x4e, %xmm3, %xmm3
vpshufd $0x4e, %xmm7, %xmm7
vpaddd %xmm0, %xmm1, %xmm0
vpaddd %xmm4, %xmm5, %xmm4
vpshufd $0x39, %xmm2, %xmm2
vpshufd $0x39, %xmm6, %xmm6
vpxor %xmm3, %xmm0, %xmm3
vpxor %xmm7, %xmm4, %xmm7
vprotd $16, %xmm3, %xmm3
vprotd $16, %xmm7, %xmm7
vpaddd %xmm2, %xmm3, %xmm2
vpaddd %xmm6, %xmm7, %xmm6
vpxor %xmm1, %xmm2, %xmm1
vpxor %xmm5, %xmm6, %xmm5
vprotd $12, %xmm1, %xmm1
vprotd $12, %xmm5, %xmm5
vpaddd %xmm0, %xmm1, %xmm0
vpaddd %xmm4, %xmm5, %xmm4
vpxor %xmm3, %xmm0, %xmm3
vpxor %xmm7, %xmm4, %xmm7
vprotd $8, %xmm3, %xmm3
vprotd $8, %xmm7, %xmm7
vpaddd %xmm2, %xmm3, %xmm2
vpaddd %xmm6, %xmm7, %xmm6
vpxor %xmm1, %xmm2, %xmm1
vpxor %xmm5, %xmm6, %xmm5
vpshufd $0x39, %xmm0, %xmm0
vpshufd $0x39, %xmm4, %xmm4
vprotd $7, %xmm1, %xmm1
vprotd $7, %xmm5, %xmm5
vpshufd $0x4e, %xmm3, %xmm3
vpshufd $0x4e, %xmm7, %xmm7
vpshufd $0x93, %xmm2, %xmm2
vpshufd $0x93, %xmm6, %xmm6
sub $2, %eax
jnz chacha_blocks_xop_mainloop2
vpaddd 0(%esp), %xmm0, %xmm0
vpaddd 0(%esp), %xmm4, %xmm4
vpaddd 16(%esp), %xmm1, %xmm1
vpaddd 16(%esp), %xmm5, %xmm5
vpaddd 32(%esp), %xmm2, %xmm2
vpaddd 32(%esp), %xmm6, %xmm6
vpaddd 48(%esp), %xmm3, %xmm3
vpaddd 448(%esp), %xmm7, %xmm7
andl %esi, %esi
jz chacha_blocks_xop_noinput2
vpxor 0(%esi), %xmm0, %xmm0
vpxor 16(%esi), %xmm1, %xmm1
vpxor 32(%esi), %xmm2, %xmm2
vpxor 48(%esi), %xmm3, %xmm3
vpxor 64(%esi), %xmm4, %xmm4
vpxor 80(%esi), %xmm5, %xmm5
vpxor 96(%esi), %xmm6, %xmm6
vpxor 112(%esi), %xmm7, %xmm7
addl $128, %esi
chacha_blocks_xop_noinput2:
vmovdqu %xmm0, 0(%edx)
vmovdqu %xmm1, 16(%edx)
vmovdqu %xmm2, 32(%edx)
vmovdqu %xmm3, 48(%edx)
vmovdqu %xmm4, 64(%edx)
vmovdqu %xmm5, 80(%edx)
vmovdqu %xmm6, 96(%edx)
vmovdqu %xmm7, 112(%edx)
movl 92(%esp), %eax
subl $128, %eax
addl $128, %edx
movl 48(%esp), %ecx
movl 4+48(%esp), %ebx
addl $2, %ecx
adcl $0, %ebx
movl %ecx, 48(%esp)
movl %ebx, 4+48(%esp)
chacha_blocks_xop_bytesbetween0and127:
andl %eax, %eax
jz chacha_blocks_xop_done
cmpl $64, %eax
jae chacha_blocks_xop_nocopy
movl %edx, 92(%esp)
cmpl $0, %esi
jbe chacha_blocks_xop_noinput3
leal 128(%esp), %edi
movl %eax, %ecx
rep movsb
leal 128(%esp), %esi
chacha_blocks_xop_noinput3:
leal 128(%esp), %edx
chacha_blocks_xop_nocopy:
movl %eax, 80(%esp)
vmovdqa 0(%esp), %xmm0
vmovdqa 16(%esp), %xmm1
vmovdqa 32(%esp), %xmm2
vmovdqa 48(%esp), %xmm3
movl 88(%esp), %eax
chacha_blocks_xop_mainloop3:
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vprotd $16, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vprotd $12, %xmm1, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vprotd $8, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpshufd $0x93, %xmm0, %xmm0
vpxor %xmm1, %xmm2, %xmm1
vprotd $7, %xmm1, %xmm1
vpshufd $0x4e, %xmm3, %xmm3
vpaddd %xmm0, %xmm1, %xmm0
vpshufd $0x39, %xmm2, %xmm2
vpxor %xmm3, %xmm0, %xmm3
vprotd $16, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vprotd $12, %xmm1, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vprotd $8, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpshufd $0x39, %xmm0, %xmm0
vprotd $7, %xmm1, %xmm1
vpshufd $0x4e, %xmm3, %xmm3
vpshufd $0x93, %xmm2, %xmm2
subl $2, %eax
ja chacha_blocks_xop_mainloop3
vpaddd 0(%esp), %xmm0, %xmm0
vpaddd 16(%esp), %xmm1, %xmm1
vpaddd 32(%esp), %xmm2, %xmm2
vpaddd 48(%esp), %xmm3, %xmm3
cmpl $0, %esi
jbe chacha_blocks_xop_noinput4
vpxor 0(%esi), %xmm0, %xmm0
vpxor 16(%esi), %xmm1, %xmm1
vpxor 32(%esi), %xmm2, %xmm2
vpxor 48(%esi), %xmm3, %xmm3
addl $64, %esi
chacha_blocks_xop_noinput4:
vmovdqu %xmm0, 0(%edx)
vmovdqu %xmm1, 16(%edx)
vmovdqu %xmm2, 32(%edx)
vmovdqu %xmm3, 48(%edx)
movl 80(%esp), %eax
movl 48(%esp), %ecx
movl 4+48(%esp), %ebx
addl $1, %ecx
adcl $0, %ebx
movl %ecx, 48(%esp)
movl %ebx, 4+48(%esp)
cmpl $64, %eax
jb chacha_blocks_xop_bytesatmost64
subl $64, %eax
addl $64, %edx
jmp chacha_blocks_xop_bytesbetween0and127
chacha_blocks_xop_bytesatmost64:
jae chacha_blocks_xop_bytesatleast64
movl %edx, %esi
movl 92(%esp), %edi
movl %eax, %ecx
rep movsb
chacha_blocks_xop_bytesatleast64:
chacha_blocks_xop_done:
movl 84(%esp), %eax
vmovdqa 48(%esp), %xmm0
vmovdqu %xmm0, 32(%eax)
movl 64(%esp), %eax
movl 68(%esp), %ebx
movl 72(%esp), %esi
movl 76(%esp), %edi
movl %ebp, %esp
popl %ebp
ret
FN_END chacha_blocks_xop


GLOBAL_HIDDEN_FN hchacha_xop
hchacha_xop_local:
LOAD_VAR_PIC chacha_constants, %eax
vmovdqa 0(%eax), %xmm0
movl 4(%esp), %eax
movl 8(%esp), %edx
vmovdqu 0(%eax), %xmm1
vmovdqu 16(%eax), %xmm2
vmovdqu 0(%edx), %xmm3
movl 12(%esp), %edx
movl 16(%esp), %ecx
hchacha_mainloop_xop:
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vprotd $16, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vprotd $12, %xmm1, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vprotd $8, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpshufd $0x93, %xmm0, %xmm0
vpxor %xmm1, %xmm2, %xmm1
vprotd $7, %xmm1, %xmm1
vpshufd $0x4e, %xmm3, %xmm3
vpaddd %xmm0, %xmm1, %xmm0
vpshufd $0x39, %xmm2, %xmm2
vpxor %xmm3, %xmm0, %xmm3
vprotd $16, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vprotd $12, %xmm1, %xmm1
vpaddd %xmm0, %xmm1, %xmm0
vpxor %xmm3, %xmm0, %xmm3
vprotd $8, %xmm3, %xmm3
vpaddd %xmm2, %xmm3, %xmm2
vpxor %xmm1, %xmm2, %xmm1
vpshufd $0x39, %xmm0, %xmm0
vprotd $7, %xmm1, %xmm1
vpshufd $0x4e, %xmm3, %xmm3
vpshufd $0x93, %xmm2, %xmm2
subl $2, %ecx
jne hchacha_mainloop_xop
vmovdqu %xmm0, (%edx)
vmovdqu %xmm3, 16(%edx)
ret
FN_END hchacha_xop

GLOBAL_HIDDEN_FN chacha_xop
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
call chacha_blocks_xop_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm0, 16(%ebx)
vmovdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END chacha_xop

GLOBAL_HIDDEN_FN xchacha_xop
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
call hchacha_xop_local
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
call chacha_blocks_xop_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm0, 16(%ebx)
vmovdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END xchacha_xop

INCLUDE_VAR_FILE "chacha/chacha_constants_x86.inc", chacha_constants

