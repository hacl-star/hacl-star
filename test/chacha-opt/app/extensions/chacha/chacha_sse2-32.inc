SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_sse2
chacha_blocks_sse2_local:
pushl %ebp
movl %esp, %ebp
andl $~63, %esp
sub $704, %esp
movl %ebx,68(%esp)
movl %esi,72(%esp)
movl %edi,76(%esp)
movl 8(%ebp),%ecx
movl %ecx,84(%esp)
movl 12(%ebp),%esi
movl 16(%ebp),%edx
movl 20(%ebp),%eax
LOAD_VAR_PIC chacha_constants, %ebx
movdqa 0(%ebx), %xmm0
movdqu 0(%ecx),%xmm1
movdqu 16(%ecx),%xmm2
movdqu 32(%ecx),%xmm3
movdqa %xmm0,0(%esp)
movdqa %xmm1,16(%esp)
movdqa %xmm2,32(%esp)
movdqa %xmm3,48(%esp)
movl 48(%ecx),%ecx
movl %ecx,88(%esp)
cmpl $0,%eax
jbe chacha_blocks_sse2_done
cmpl $256,%eax
jb chacha_blocks_sse2_bytesbetween1and255
pshufd $0x00, %xmm0, %xmm4
pshufd $0x55, %xmm0, %xmm5
pshufd $0xaa, %xmm0, %xmm6
pshufd $0xff, %xmm0, %xmm0
movdqa %xmm4,128(%esp)
movdqa %xmm5,144(%esp)
movdqa %xmm6,160(%esp)
movdqa %xmm0,176(%esp)
pshufd $0x00, %xmm1, %xmm0
pshufd $0x55, %xmm1, %xmm4
pshufd $0xaa, %xmm1, %xmm5
pshufd $0xff, %xmm1, %xmm1
movdqa %xmm0,192(%esp)
movdqa %xmm4,208(%esp)
movdqa %xmm5,224(%esp)
movdqa %xmm1,240(%esp)
pshufd $0x00, %xmm2, %xmm0
pshufd $0x55, %xmm2, %xmm1
pshufd $0xaa, %xmm2, %xmm4
pshufd $0xff, %xmm2, %xmm2
movdqa %xmm0,256(%esp)
movdqa %xmm1,272(%esp)
movdqa %xmm4,288(%esp)
movdqa %xmm2,304(%esp)
pshufd $0xaa, %xmm3, %xmm0
pshufd $0xff, %xmm3, %xmm1
movdqa %xmm0,352(%esp)
movdqa %xmm1,368(%esp)
chacha_blocks_sse2_bytesatleast256:
movl 48(%esp),%ecx
movl 4+48(%esp),%ebx
movl %ecx,320(%esp)
movl %ebx,336(%esp)
addl $1,%ecx
adcl $0,%ebx
movl %ecx,4+320(%esp)
movl %ebx,4+336(%esp)
addl $1,%ecx
adcl $0,%ebx
movl %ecx,8+320(%esp)
movl %ebx,8+336(%esp)
addl $1,%ecx
adcl $0,%ebx
movl %ecx,12+320(%esp)
movl %ebx,12+336(%esp)
addl $1,%ecx
adcl $0,%ebx
movl %ecx,48(%esp)
movl %ebx,4+48(%esp)
movl %eax,92(%esp)
movl 88(%esp),%eax
movdqa 160(%esp),%xmm0
movdqa 224(%esp),%xmm1
movdqa 288(%esp),%xmm2
movdqa 352(%esp),%xmm3
movdqa 176(%esp),%xmm4
movdqa 240(%esp),%xmm5
movdqa 304(%esp),%xmm6
movdqa 368(%esp),%xmm7
movdqa %xmm0,480(%esp)
movdqa %xmm1,544(%esp)
movdqa %xmm2,608(%esp)
movdqa %xmm3,672(%esp)
movdqa %xmm4,496(%esp)
movdqa %xmm5,560(%esp)
movdqa %xmm6,624(%esp)
movdqa %xmm7,688(%esp)
movdqa 128(%esp),%xmm0
movdqa 192(%esp),%xmm1
movdqa 256(%esp),%xmm2
movdqa 320(%esp),%xmm3
movdqa 144(%esp),%xmm4
movdqa 208(%esp),%xmm5
movdqa 272(%esp),%xmm6
movdqa 336(%esp),%xmm7
jmp chacha_blocks_sse2_mainloop1
.p2align 6
chacha_blocks_sse2_mainloop1:
paddd %xmm1, %xmm0
paddd %xmm5, %xmm4
pxor %xmm0, %xmm3
pxor %xmm4, %xmm7
pshuflw $0xb1,%xmm3,%xmm3
pshuflw $0xb1,%xmm7,%xmm7
pshufhw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm7,%xmm7
movdqa %xmm4, 464(%esp)
paddd %xmm3, %xmm2
paddd %xmm7, %xmm6
pxor %xmm2, %xmm1
pxor %xmm6, %xmm5
movdqa %xmm1, %xmm4
pslld $12, %xmm1
psrld $20, %xmm4
por %xmm4, %xmm1
movdqa %xmm5, %xmm4
pslld $12, %xmm5
psrld $20, %xmm4
por %xmm4, %xmm5
movdqa 464(%esp), %xmm4
paddd %xmm1, %xmm0
paddd %xmm5, %xmm4
pxor %xmm0, %xmm3
pxor %xmm4, %xmm7
movdqa %xmm0, 448(%esp)
movdqa %xmm4, 464(%esp)
movdqa %xmm3, %xmm4
pslld $8, %xmm3
psrld $24, %xmm4
por %xmm4, %xmm3
movdqa %xmm7, %xmm4
pslld $8, %xmm7
psrld $24, %xmm4
por %xmm4, %xmm7
paddd %xmm3, %xmm2
paddd %xmm7, %xmm6
movdqa %xmm3, 640(%esp)
movdqa %xmm7, 656(%esp)
pxor %xmm2, %xmm1
pxor %xmm6, %xmm5
movdqa %xmm2, 576(%esp)
movdqa %xmm6, 592(%esp)
movdqa %xmm1,%xmm4
pslld $7, %xmm1
movdqa 672(%esp), %xmm3
psrld $25, %xmm4
movdqa 688(%esp), %xmm7
por %xmm4, %xmm1
movdqa %xmm1, 512(%esp)
movdqa %xmm5, %xmm0
pslld $7, %xmm5
movdqa 608(%esp), %xmm2
psrld $25, %xmm0
movdqa 624(%esp), %xmm6
por %xmm0, %xmm5
movdqa %xmm5, 528(%esp)
movdqa 480(%esp), %xmm0
movdqa 496(%esp), %xmm4
movdqa 544(%esp), %xmm1
movdqa 560(%esp), %xmm5
paddd %xmm1, %xmm0
paddd %xmm5, %xmm4
pxor %xmm0, %xmm3
pxor %xmm4, %xmm7
pshuflw $0xb1,%xmm3,%xmm3
pshuflw $0xb1,%xmm7,%xmm7
pshufhw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm7,%xmm7
movdqa %xmm4, 496(%esp)
paddd %xmm3, %xmm2
paddd %xmm7, %xmm6
pxor %xmm2, %xmm1
pxor %xmm6, %xmm5
movdqa %xmm1, %xmm4
pslld $12, %xmm1
psrld $20, %xmm4
por %xmm4, %xmm1
movdqa %xmm5, %xmm4
pslld $12, %xmm5
psrld $20, %xmm4
por %xmm4, %xmm5
movdqa 496(%esp), %xmm4
paddd %xmm1, %xmm0
paddd %xmm5, %xmm4
pxor %xmm0, %xmm3
pxor %xmm4, %xmm7
movdqa %xmm0, 480(%esp)
movdqa %xmm4, 496(%esp)
movdqa %xmm3, %xmm4
pslld $8, %xmm3
psrld $24, %xmm4
por %xmm4, %xmm3
movdqa %xmm7, %xmm4
pslld $8, %xmm7
psrld $24, %xmm4
por %xmm4, %xmm7
paddd %xmm3, %xmm2
paddd %xmm7, %xmm6
movdqa %xmm3, 672(%esp)
pxor %xmm2, %xmm1
pxor %xmm6, %xmm5
movdqa %xmm1,%xmm4
pslld $7, %xmm1
psrld $25, %xmm4
movdqa 640(%esp), %xmm3
por %xmm4, %xmm1
movdqa %xmm5, %xmm0
pslld $7, %xmm5
psrld $25, %xmm0
por %xmm0, %xmm5
movdqa %xmm5, 560(%esp)
movdqa 448(%esp), %xmm0
movdqa 528(%esp), %xmm5
movdqa 464(%esp), %xmm4
paddd %xmm5, %xmm0
paddd %xmm1, %xmm4
pxor %xmm0, %xmm7
pxor %xmm4, %xmm3
pshuflw $0xb1,%xmm7,%xmm7
pshuflw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm7,%xmm7
pshufhw $0xb1,%xmm3,%xmm3
movdqa %xmm4, 464(%esp)
paddd %xmm7, %xmm2
paddd %xmm3, %xmm6
pxor %xmm2, %xmm5
pxor %xmm6, %xmm1
movdqa %xmm5, %xmm4
pslld $12, %xmm5
psrld $20, %xmm4
por %xmm4, %xmm5
movdqa %xmm1, %xmm4
pslld $12, %xmm1
psrld $20, %xmm4
por %xmm4, %xmm1
movdqa 464(%esp), %xmm4
paddd %xmm5, %xmm0
paddd %xmm1, %xmm4
pxor %xmm0, %xmm7
pxor %xmm4, %xmm3
movdqa %xmm0, 448(%esp)
movdqa %xmm4, 464(%esp)
movdqa %xmm7, %xmm4
pslld $8, %xmm7
psrld $24, %xmm4
por %xmm4, %xmm7
movdqa %xmm3, %xmm4
pslld $8, %xmm3
psrld $24, %xmm4
por %xmm4, %xmm3
paddd %xmm7, %xmm2
paddd %xmm3, %xmm6
movdqa %xmm7, 688(%esp)
movdqa %xmm3, 640(%esp)
pxor %xmm2, %xmm5
pxor %xmm6, %xmm1
movdqa %xmm2, 608(%esp)
movdqa %xmm6, 624(%esp)
movdqa %xmm5,%xmm4
pslld $7, %xmm5
movdqa 656(%esp), %xmm7
psrld $25, %xmm4
movdqa 672(%esp), %xmm3
por %xmm4, %xmm5
movdqa %xmm5, 528(%esp)
movdqa %xmm1, %xmm0
pslld $7, %xmm1
movdqa 576(%esp), %xmm2
psrld $25, %xmm0
movdqa 592(%esp), %xmm6
por %xmm0, %xmm1
movdqa %xmm1, 544(%esp)
movdqa 480(%esp), %xmm0
movdqa 496(%esp), %xmm4
movdqa 560(%esp), %xmm5
movdqa 512(%esp), %xmm1
paddd %xmm5, %xmm0
paddd %xmm1, %xmm4
pxor %xmm0, %xmm7
pxor %xmm4, %xmm3
pshuflw $0xb1,%xmm7,%xmm7
pshuflw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm7,%xmm7
pshufhw $0xb1,%xmm3,%xmm3
movdqa %xmm4, 496(%esp)
paddd %xmm7, %xmm2
paddd %xmm3, %xmm6
pxor %xmm2, %xmm5
pxor %xmm6, %xmm1
movdqa %xmm5, %xmm4
pslld $12, %xmm5
psrld $20, %xmm4
por %xmm4, %xmm5
movdqa %xmm1, %xmm4
pslld $12, %xmm1
psrld $20, %xmm4
por %xmm4, %xmm1
movdqa 496(%esp), %xmm4
paddd %xmm5, %xmm0
paddd %xmm1, %xmm4
pxor %xmm0, %xmm7
pxor %xmm4, %xmm3
movdqa %xmm0, 480(%esp)
movdqa %xmm4, 496(%esp)
movdqa %xmm7, %xmm4
pslld $8, %xmm7
psrld $24, %xmm4
por %xmm4, %xmm7
movdqa %xmm3, %xmm4
pslld $8, %xmm3
psrld $24, %xmm4
por %xmm4, %xmm3
paddd %xmm7, %xmm2
paddd %xmm3, %xmm6
movdqa %xmm3, 672(%esp)
pxor %xmm2, %xmm5
pxor %xmm6, %xmm1
movdqa %xmm5,%xmm4
pslld $7, %xmm5
psrld $25, %xmm4
movdqa 640(%esp), %xmm3
por %xmm4, %xmm5
movdqa %xmm5, 560(%esp)
movdqa %xmm1, %xmm0
pslld $7, %xmm1
psrld $25, %xmm0
por %xmm0, %xmm1
movdqa 448(%esp), %xmm0
movdqa 464(%esp), %xmm4
movdqa 528(%esp), %xmm5
subl $2,%eax
ja chacha_blocks_sse2_mainloop1
movdqa %xmm0, 448(%esp)
movdqa %xmm1, 512(%esp)
movdqa %xmm2, 576(%esp)
movdqa %xmm3, 640(%esp)
movdqa %xmm4, 464(%esp)
movdqa %xmm5, 528(%esp)
movdqa %xmm6, 592(%esp)
movdqa %xmm7, 656(%esp)
cmpl $0,%esi
movdqa 448(%esp),%xmm0
movdqa 464(%esp),%xmm1
movdqa 480(%esp),%xmm2
movdqa 496(%esp),%xmm3
paddd 128(%esp), %xmm0
paddd 144(%esp), %xmm1
paddd 160(%esp), %xmm2
paddd 176(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
jbe chacha_blocks_sse2_noinput1
movdqu 0(%esi), %xmm2
movdqu 64(%esi), %xmm5
movdqu 128(%esi), %xmm6
movdqu 192(%esi), %xmm7
pxor %xmm2, %xmm4
pxor %xmm5, %xmm1
pxor %xmm6, %xmm0
pxor %xmm7, %xmm3
movdqu %xmm4, 0(%edx)
movdqu %xmm1, 64(%edx)
movdqu %xmm0, 128(%edx)
movdqu %xmm3, 192(%edx)
movdqa 512(%esp),%xmm0
movdqa 528(%esp),%xmm1
movdqa 544(%esp),%xmm2
movdqa 560(%esp),%xmm3
paddd 192(%esp), %xmm0
paddd 208(%esp), %xmm1
paddd 224(%esp), %xmm2
paddd 240(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
movdqu 16+0(%esi), %xmm2
movdqu 16+64(%esi), %xmm5
movdqu 16+128(%esi), %xmm6
movdqu 16+192(%esi), %xmm7
pxor %xmm2, %xmm4
pxor %xmm5, %xmm1
pxor %xmm6, %xmm0
pxor %xmm7, %xmm3
movdqu %xmm4, 16+0(%edx)
movdqu %xmm1, 16+64(%edx)
movdqu %xmm0, 16+128(%edx)
movdqu %xmm3, 16+192(%edx)
movdqa 576(%esp),%xmm0
movdqa 592(%esp),%xmm1
movdqa 608(%esp),%xmm2
movdqa 624(%esp),%xmm3
paddd 256(%esp), %xmm0
paddd 272(%esp), %xmm1
paddd 288(%esp), %xmm2
paddd 304(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
movdqu 32+0(%esi), %xmm2
movdqu 32+64(%esi), %xmm5
movdqu 32+128(%esi), %xmm6
movdqu 32+192(%esi), %xmm7
pxor %xmm2, %xmm4
pxor %xmm5, %xmm1
pxor %xmm6, %xmm0
pxor %xmm7, %xmm3
movdqu %xmm4, 32+0(%edx)
movdqu %xmm1, 32+64(%edx)
movdqu %xmm0, 32+128(%edx)
movdqu %xmm3, 32+192(%edx)
movdqa 640(%esp),%xmm0
movdqa 656(%esp),%xmm1
movdqa 672(%esp),%xmm2
movdqa 688(%esp),%xmm3
paddd 320(%esp), %xmm0
paddd 336(%esp), %xmm1
paddd 352(%esp), %xmm2
paddd 368(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
movdqu 48+0(%esi), %xmm2
movdqu 48+64(%esi), %xmm5
movdqu 48+128(%esi), %xmm6
movdqu 48+192(%esi), %xmm7
pxor %xmm2, %xmm4
pxor %xmm5, %xmm1
pxor %xmm6, %xmm0
pxor %xmm7, %xmm3
movdqu %xmm4, 48+0(%edx)
movdqu %xmm1, 48+64(%edx)
movdqu %xmm0, 48+128(%edx)
movdqu %xmm3, 48+192(%edx)
addl $256,%esi
jmp chacha_blocks_sse2_mainloop1_cont
chacha_blocks_sse2_noinput1:
movdqu %xmm4, 0(%edx)
movdqu %xmm1, 64(%edx)
movdqu %xmm0, 128(%edx)
movdqu %xmm3, 192(%edx)
movdqa 512(%esp),%xmm0
movdqa 528(%esp),%xmm1
movdqa 544(%esp),%xmm2
movdqa 560(%esp),%xmm3
paddd 192(%esp), %xmm0
paddd 208(%esp), %xmm1
paddd 224(%esp), %xmm2
paddd 240(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
movdqu %xmm4, 16+0(%edx)
movdqu %xmm1, 16+64(%edx)
movdqu %xmm0, 16+128(%edx)
movdqu %xmm3, 16+192(%edx)
movdqa 576(%esp),%xmm0
movdqa 592(%esp),%xmm1
movdqa 608(%esp),%xmm2
movdqa 624(%esp),%xmm3
paddd 256(%esp), %xmm0
paddd 272(%esp), %xmm1
paddd 288(%esp), %xmm2
paddd 304(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
movdqu %xmm4, 32+0(%edx)
movdqu %xmm1, 32+64(%edx)
movdqu %xmm0, 32+128(%edx)
movdqu %xmm3, 32+192(%edx)
movdqa 640(%esp),%xmm0
movdqa 656(%esp),%xmm1
movdqa 672(%esp),%xmm2
movdqa 688(%esp),%xmm3
paddd 320(%esp), %xmm0
paddd 336(%esp), %xmm1
paddd 352(%esp), %xmm2
paddd 368(%esp), %xmm3
movdqa %xmm0, %xmm4
movdqa %xmm2, %xmm5
punpckldq %xmm1, %xmm4
punpckldq %xmm3, %xmm5
punpckhdq %xmm1, %xmm0
punpckhdq %xmm3, %xmm2
movdqa %xmm4, %xmm1
movdqa %xmm0, %xmm3
punpcklqdq %xmm5, %xmm4
punpckhqdq %xmm5, %xmm1
punpcklqdq %xmm2, %xmm0
punpckhqdq %xmm2, %xmm3
movdqu %xmm4, 48+0(%edx)
movdqu %xmm1, 48+64(%edx)
movdqu %xmm0, 48+128(%edx)
movdqu %xmm3, 48+192(%edx)
chacha_blocks_sse2_mainloop1_cont:
movl 92(%esp),%eax
subl $256,%eax
addl $256,%edx
cmpl $256,%eax
jae chacha_blocks_sse2_bytesatleast256
cmpl $0,%eax
jbe chacha_blocks_sse2_done
chacha_blocks_sse2_bytesbetween1and255:
cmpl $64,%eax
jae chacha_blocks_sse2_nocopy
movl %edx,92(%esp)
cmpl $0,%esi
jbe chacha_blocks_sse2_noinput2
leal 128(%esp),%edi
movl %eax,%ecx
rep movsb
leal 128(%esp),%esi
chacha_blocks_sse2_noinput2:
leal 128(%esp),%edx
chacha_blocks_sse2_nocopy:
movl %eax,80(%esp)
movdqa 0(%esp),%xmm0
movdqa 16(%esp),%xmm1
movdqa 32(%esp),%xmm2
movdqa 48(%esp),%xmm3
movl 88(%esp),%eax
chacha_blocks_sse2_mainloop2:
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
pshuflw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm3,%xmm3
paddd %xmm3, %xmm2
pxor %xmm2, %xmm1
movdqa %xmm1,%xmm4
pslld $12, %xmm1
psrld $20, %xmm4
pxor %xmm4, %xmm1
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
movdqa %xmm3,%xmm4
pslld $8, %xmm3
psrld $24, %xmm4
pshufd $0x93,%xmm0,%xmm0
pxor %xmm4, %xmm3
paddd %xmm3, %xmm2
pshufd $0x4e,%xmm3,%xmm3
pxor %xmm2, %xmm1
pshufd $0x39,%xmm2,%xmm2
movdqa %xmm1,%xmm4
pslld $7, %xmm1
psrld $25, %xmm4
pxor %xmm4, %xmm1
subl $2, %eax
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
pshuflw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm3,%xmm3
paddd %xmm3, %xmm2
pxor %xmm2, %xmm1
movdqa %xmm1,%xmm4
pslld $12, %xmm1
psrld $20, %xmm4
pxor %xmm4, %xmm1
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
movdqa %xmm3,%xmm4
pslld $8, %xmm3
psrld $24, %xmm4
pshufd $0x39,%xmm0,%xmm0
pxor %xmm4, %xmm3
paddd %xmm3, %xmm2
pshufd $0x4e,%xmm3,%xmm3
pxor %xmm2, %xmm1
pshufd $0x93,%xmm2,%xmm2
movdqa %xmm1,%xmm4
pslld $7, %xmm1
psrld $25, %xmm4
pxor %xmm4, %xmm1
ja chacha_blocks_sse2_mainloop2
paddd 0(%esp), %xmm0
paddd 16(%esp), %xmm1
paddd 32(%esp), %xmm2
paddd 48(%esp), %xmm3
cmpl $0,%esi
jbe chacha_blocks_sse2_noinput3
movdqu 0(%esi),%xmm4
movdqu 16(%esi),%xmm5
movdqu 32(%esi),%xmm6
movdqu 48(%esi),%xmm7
pxor %xmm4, %xmm0
pxor %xmm5, %xmm1
pxor %xmm6, %xmm2
pxor %xmm7, %xmm3
addl $64,%esi
chacha_blocks_sse2_noinput3:
movdqu %xmm0,0(%edx)
movdqu %xmm1,16(%edx)
movdqu %xmm2,32(%edx)
movdqu %xmm3,48(%edx)
movl 80(%esp),%eax
movl 48(%esp),%ecx
movl 4+48(%esp),%ebx
addl $1,%ecx
adcl $0,%ebx
movl %ecx,48(%esp)
movl %ebx,4+48(%esp)
cmpl $64,%eax
ja chacha_blocks_sse2_bytesatleast65
jae chacha_blocks_sse2_bytesatleast64
movl %edx,%esi
movl 92(%esp),%edi
movl %eax,%ecx
rep movsb
chacha_blocks_sse2_bytesatleast64:
chacha_blocks_sse2_done:
movl 84(%esp),%eax
movdqa 48(%esp),%xmm0
movdqu %xmm0,32(%eax)
movl 64(%esp),%eax
movl 68(%esp),%ebx
movl 72(%esp),%esi
movl 76(%esp),%edi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_sse2_bytesatleast65:
subl $64,%eax
addl $64,%edx
jmp chacha_blocks_sse2_bytesbetween1and255
FN_END chacha_blocks_sse2


GLOBAL_HIDDEN_FN hchacha_sse2
hchacha_sse2_local:
LOAD_VAR_PIC chacha_constants, %eax
movdqa 0(%eax), %xmm0
movl 4(%esp), %eax
movl 8(%esp), %edx
movdqu 0(%eax), %xmm1
movdqu 16(%eax), %xmm2
movdqu 0(%edx), %xmm3
movl 12(%esp), %edx
movl 16(%esp), %ecx
hchacha_sse2_mainloop: 
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
pshuflw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm3,%xmm3
paddd %xmm3, %xmm2
pxor %xmm2, %xmm1
movdqa %xmm1,%xmm4
pslld $12, %xmm1
psrld $20, %xmm4
pxor %xmm4, %xmm1
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
movdqa %xmm3,%xmm4
pslld $8, %xmm3
psrld $24, %xmm4
pshufd $0x93,%xmm0,%xmm0
pxor %xmm4, %xmm3
paddd %xmm3, %xmm2
pshufd $0x4e,%xmm3,%xmm3
pxor %xmm2, %xmm1
pshufd $0x39,%xmm2,%xmm2
movdqa %xmm1,%xmm4
pslld $7, %xmm1
psrld $25, %xmm4
pxor %xmm4, %xmm1
subl $2, %ecx
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
pshuflw $0xb1,%xmm3,%xmm3
pshufhw $0xb1,%xmm3,%xmm3
paddd %xmm3, %xmm2
pxor %xmm2, %xmm1
movdqa %xmm1,%xmm4
pslld $12, %xmm1
psrld $20, %xmm4
pxor %xmm4, %xmm1
paddd %xmm1, %xmm0
pxor %xmm0, %xmm3
movdqa %xmm3,%xmm4
pslld $8, %xmm3
psrld $24, %xmm4
pshufd $0x39,%xmm0,%xmm0
pxor %xmm4, %xmm3
paddd %xmm3, %xmm2
pshufd $0x4e,%xmm3,%xmm3
pxor %xmm2, %xmm1
pshufd $0x93,%xmm2,%xmm2
movdqa %xmm1,%xmm4
pslld $7, %xmm1
psrld $25, %xmm4
pxor %xmm4, %xmm1
ja hchacha_sse2_mainloop
movdqu %xmm0, 0(%edx)
movdqu %xmm3, 16(%edx)
ret
FN_END hchacha_sse2

GLOBAL_HIDDEN_FN chacha_sse2
pushl %ebp
pushl %ebx
movl %esp, %ebp
subl $64, %esp
andl $~63, %esp
movl %esp, %ebx
movl 12(%ebp), %ecx
xorl %edx, %edx
movdqu 0(%ecx), %xmm0
movdqu 16(%ecx), %xmm1
movdqa %xmm0, 0(%ebx)
movdqa %xmm1, 16(%ebx)
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
call chacha_blocks_sse2_local
pxor %xmm0, %xmm0
movdqa %xmm0, 0(%ebx)
movdqa %xmm0, 16(%ebx)
movdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END chacha_sse2

GLOBAL_HIDDEN_FN xchacha_sse2
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
call hchacha_sse2_local
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
call chacha_blocks_sse2_local
pxor %xmm0, %xmm0
movdqa %xmm0, 0(%ebx)
movdqa %xmm0, 16(%ebx)
movdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END xchacha_sse2

INCLUDE_VAR_FILE "chacha/chacha_constants_x86.inc", chacha_constants

