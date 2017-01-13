SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_avx2
chacha_blocks_avx2_local:
pushl %ebp
movl %esp, %ebp
andl $~63, %esp
pushl %esi
pushl %edi
pushl %ebx
subl $3124, %esp
movl $1, %eax
LOAD_VAR_PIC chacha_constants, %esi
movl 16(%ebp), %ebx
movl 20(%ebp), %edx
vmovd %eax, %xmm0
vmovdqu 16(%esi), %ymm1
vmovdqu 32(%esi), %ymm2
vmovdqu %xmm0, 592(%esp)
vmovdqu %ymm1, 1568(%esp)
vmovdqu %ymm2, 1536(%esp)
movl 12(%ebp), %edi
movl %ebx, 1508(%esp)
testl %edx, %edx
je chacha_blocks_avx2_44
chacha_blocks_avx2_2:
movl 8(%ebp), %ecx
vmovdqu 0(%esi), %xmm5
vmovdqu %xmm5, 544(%esp)
vmovdqu 16(%ecx), %xmm0
vmovdqu (%ecx), %xmm1
vmovdqu %xmm0, 576(%esp)
vmovdqu 32(%ecx), %xmm0
movl 48(%ecx), %eax
vmovdqu %xmm1, 560(%esp)
movl %eax, 1516(%esp)
vmovq 8(%esi), %xmm5
vmovq 8(%ecx), %xmm1
vmovdqu %xmm0, 304(%esp)
vpsrldq $4, %xmm0, %xmm2
cmpl $512, %edx
jb chacha_blocks_avx2_10
chacha_blocks_avx2_3:
vpbroadcastd 312(%esp), %ymm7
vmovdqu 576(%esp), %xmm4
vmovdqu %ymm7, 704(%esp)
vmovdqu %xmm4, 288(%esp)
vmovdqu 560(%esp), %xmm6
vmovdqu 544(%esp), %xmm3
vmovdqu %xmm6, 272(%esp)
vpbroadcastd 316(%esp), %ymm7
vmovdqu %ymm7, 672(%esp)
vmovdqu %xmm3, 256(%esp)
vmovd %xmm0, %ecx
vmovd %xmm2, %eax
vpbroadcastd 292(%esp), %ymm7
vmovdqu %ymm7, 800(%esp)
vpbroadcastd %xmm4, %ymm0
vpbroadcastd %xmm1, %ymm1
vpbroadcastd 296(%esp), %ymm7
vmovdqu %ymm0, 832(%esp)
vmovdqu %ymm1, 864(%esp)
vmovdqu %ymm7, 768(%esp)
vpbroadcastd %xmm3, %ymm2
vpbroadcastd %xmm6, %ymm3
vpbroadcastd 260(%esp), %ymm0
vpbroadcastd 276(%esp), %ymm4
vpbroadcastd 284(%esp), %ymm1
vpbroadcastd 300(%esp), %ymm7
vpbroadcastd %xmm5, %ymm6
vpbroadcastd 268(%esp), %ymm5
vmovdqu %ymm7, 736(%esp)
vmovdqu %ymm1, 1088(%esp)
vmovdqu %ymm4, 1056(%esp)
vmovdqu %ymm3, 1024(%esp)
vmovdqu %ymm5, 992(%esp)
vmovdqu %ymm6, 960(%esp)
vmovdqu %ymm0, 928(%esp)
vmovdqu %ymm2, 896(%esp)
movl %edx, 1512(%esp)
movl %esi, 1504(%esp)
chacha_blocks_avx2_4:
movl %ecx, %edx
movl %eax, %esi
addl $1, %edx
movl %edx, 612(%esp)
movl %ecx, %edx
adcl $0, %esi
addl $2, %edx
movl %esi, 644(%esp)
movl %eax, %esi
movl %edx, 616(%esp)
movl %ecx, %edx
adcl $0, %esi
addl $3, %edx
movl %esi, 648(%esp)
movl %eax, %esi
movl %edx, 620(%esp)
movl %ecx, %edx
vmovdqu 864(%esp), %ymm3
adcl $0, %esi
vmovdqu 832(%esp), %ymm7
vmovdqu 896(%esp), %ymm2
vmovdqu 960(%esp), %ymm5
vmovdqu 1056(%esp), %ymm6
vmovdqu %ymm3, 1760(%esp)
vmovdqu 800(%esp), %ymm3
vmovdqu %ymm7, 1248(%esp)
vmovdqu 768(%esp), %ymm7
vmovdqu 928(%esp), %ymm4
vmovdqu %ymm6, 1792(%esp)
vmovdqu %ymm3, 1216(%esp)
vmovdqu 736(%esp), %ymm3
vmovdqu %ymm7, 1728(%esp)
vmovdqu 704(%esp), %ymm7
vmovdqu %ymm5, 1888(%esp)
vmovdqu %ymm2, 1824(%esp)
vmovdqu %ymm3, 1696(%esp)
vmovdqu 672(%esp), %ymm3
vmovdqu 1088(%esp), %ymm6
vmovdqu 1248(%esp), %ymm2
vmovdqu %ymm7, 1632(%esp)
vmovdqu %ymm4, 1856(%esp)
vmovdqu %ymm3, 1600(%esp)
addl $4, %edx
movl %esi, 652(%esp)
movl %eax, %esi
movl %edx, 624(%esp)
movl %ecx, %edx
adcl $0, %esi
addl $5, %edx
movl %esi, 656(%esp)
movl %eax, %esi
movl %edx, 628(%esp)
movl %ecx, %edx
adcl $0, %esi
addl $6, %edx
movl %esi, 660(%esp)
movl %eax, %esi
movl %edx, 632(%esp)
movl %ecx, %edx
adcl $0, %esi
addl $7, %edx
movl %esi, 664(%esp)
movl %eax, %esi
adcl $0, %esi
movl %eax, 640(%esp)
movl %esi, 668(%esp)
vmovdqu 640(%esp), %ymm1
movl %ecx, 608(%esp)
addl $8, %ecx
movl %edx, 636(%esp)
vmovdqu %ymm1, 1120(%esp)
adcl $0, %eax
vmovdqu %ymm1, 1184(%esp)
vmovdqu 608(%esp), %ymm0
vmovdqu 992(%esp), %ymm1
vmovdqu 1184(%esp), %ymm5
vmovdqu %ymm0, 1152(%esp)
vmovdqu %ymm0, 1664(%esp)
vmovdqu %ymm1, 1920(%esp)
vmovdqu 1024(%esp), %ymm0
vmovdqu 1216(%esp), %ymm1
movl 1516(%esp), %edx
movl %ecx, 304(%esp)
movl %eax, 308(%esp)
jmp chacha_blocks_avx2_5
.p2align 6
nop
nop
nop
nop
nop
chacha_blocks_avx2_5:
vmovdqu 1792(%esp), %ymm7
vmovdqu %ymm6, 1952(%esp)
vpaddd 1824(%esp), %ymm0, %ymm3
vpaddd 1920(%esp), %ymm6, %ymm6
vpaddd 1856(%esp), %ymm7, %ymm7
vpxor 1664(%esp), %ymm3, %ymm4
vmovdqu %ymm3, 1984(%esp)
vmovdqu 1568(%esp), %ymm3
vmovdqu %ymm7, 2016(%esp)
vmovdqu %ymm6, 2080(%esp)
vpxor %ymm7, %ymm5, %ymm5
vpxor 1600(%esp), %ymm6, %ymm6
vmovdqu 1760(%esp), %ymm7
vpshufb %ymm3, %ymm4, %ymm4
vpshufb %ymm3, %ymm5, %ymm5
vpshufb %ymm3, %ymm6, %ymm6
vpaddd 1888(%esp), %ymm7, %ymm7
vpaddd %ymm4, %ymm2, %ymm2
vpaddd %ymm5, %ymm1, %ymm1
vmovdqu %ymm6, 2112(%esp)
vmovdqu %ymm7, 2048(%esp)
vmovdqu %ymm2, 2144(%esp)
vmovdqu %ymm1, 2176(%esp)
vpxor 1632(%esp), %ymm7, %ymm7
vpxor %ymm2, %ymm0, %ymm0
vpxor 1792(%esp), %ymm1, %ymm1
vpshufb %ymm3, %ymm7, %ymm7
vpsrld $20, %ymm0, %ymm2
vpslld $12, %ymm0, %ymm3
vpor %ymm3, %ymm2, %ymm0
vpsrld $20, %ymm1, %ymm2
vpslld $12, %ymm1, %ymm1
vpaddd 1696(%esp), %ymm6, %ymm3
vmovdqu %ymm0, 2208(%esp)
vpor %ymm1, %ymm2, %ymm2
vpaddd 1728(%esp), %ymm7, %ymm1
vmovdqu %ymm3, 2272(%esp)
vpxor 1760(%esp), %ymm1, %ymm6
vmovdqu %ymm1, 2240(%esp)
vpxor 1952(%esp), %ymm3, %ymm1
vpsrld $20, %ymm6, %ymm3
vpslld $12, %ymm6, %ymm6
vpor %ymm6, %ymm3, %ymm3
vpsrld $20, %ymm1, %ymm6
vpslld $12, %ymm1, %ymm1
vmovdqu %ymm3, 2304(%esp)
vpor %ymm1, %ymm6, %ymm1
vpaddd 1984(%esp), %ymm0, %ymm6
vpaddd 2016(%esp), %ymm2, %ymm0
vmovdqu %ymm6, 2336(%esp)
vmovdqu %ymm0, 2368(%esp)
vpxor %ymm6, %ymm4, %ymm6
vpxor %ymm0, %ymm5, %ymm5
vpaddd 2048(%esp), %ymm3, %ymm0
vmovdqu 1536(%esp), %ymm4
vpxor %ymm0, %ymm7, %ymm7
vmovdqu %ymm0, 2464(%esp)
vpshufb %ymm4, %ymm6, %ymm6
vpshufb %ymm4, %ymm5, %ymm5
vpshufb %ymm4, %ymm7, %ymm0
vmovdqu %ymm6, 2400(%esp)
vmovdqu %ymm5, 2432(%esp)
vmovdqu %ymm0, 2528(%esp)
vpaddd 2080(%esp), %ymm1, %ymm6
vpaddd 2176(%esp), %ymm5, %ymm5
vpaddd 2240(%esp), %ymm0, %ymm0
vmovdqu %ymm6, 2496(%esp)
vmovdqu %ymm5, 2592(%esp)
vpxor 2112(%esp), %ymm6, %ymm6
vpxor %ymm5, %ymm2, %ymm5
vpshufb %ymm4, %ymm6, %ymm6
vmovdqu 2400(%esp), %ymm4
vpaddd 2144(%esp), %ymm4, %ymm7
vpxor 2208(%esp), %ymm7, %ymm3
vmovdqu %ymm7, 2560(%esp)
vpsrld $25, %ymm3, %ymm2
vpslld $7, %ymm3, %ymm4
vpor %ymm4, %ymm2, %ymm7
vpsrld $25, %ymm5, %ymm2
vpslld $7, %ymm5, %ymm5
vpaddd 2272(%esp), %ymm6, %ymm4
vmovdqu %ymm7, 2624(%esp)
vpor %ymm5, %ymm2, %ymm3
vpxor 2304(%esp), %ymm0, %ymm2
vpxor %ymm4, %ymm1, %ymm1
vmovdqu %ymm4, 2688(%esp)
vmovdqu %ymm3, 2656(%esp)
vpsrld $25, %ymm2, %ymm5
vpslld $7, %ymm2, %ymm2
vpsrld $25, %ymm1, %ymm4
vpslld $7, %ymm1, %ymm1
vpor %ymm2, %ymm5, %ymm2
vpor %ymm1, %ymm4, %ymm5
vpaddd 2336(%esp), %ymm3, %ymm1
vpaddd 2368(%esp), %ymm2, %ymm3
vmovdqu %ymm5, 2720(%esp)
vmovdqu %ymm1, 2752(%esp)
vmovdqu %ymm3, 2784(%esp)
vpxor %ymm1, %ymm6, %ymm4
vpxor 2400(%esp), %ymm3, %ymm3
vmovdqu 1568(%esp), %ymm6
vpshufb %ymm6, %ymm4, %ymm1
vpshufb %ymm6, %ymm3, %ymm3
vpaddd 2464(%esp), %ymm5, %ymm4
vpaddd 2496(%esp), %ymm7, %ymm5
vpaddd %ymm1, %ymm0, %ymm0
vpxor 2432(%esp), %ymm4, %ymm7
vmovdqu %ymm5, 2848(%esp)
vmovdqu %ymm0, 2912(%esp)
vmovdqu %ymm4, 2816(%esp)
vpxor 2528(%esp), %ymm5, %ymm5
vpxor 2656(%esp), %ymm0, %ymm0
vpshufb %ymm6, %ymm7, %ymm7
vpshufb %ymm6, %ymm5, %ymm4
vpaddd 2688(%esp), %ymm3, %ymm6
vpsrld $20, %ymm0, %ymm5
vmovdqu %ymm4, 2880(%esp)
vpxor %ymm6, %ymm2, %ymm2
vmovdqu %ymm6, 2944(%esp)
vpslld $12, %ymm0, %ymm6
vpor %ymm6, %ymm5, %ymm0
vpsrld $20, %ymm2, %ymm5
vpslld $12, %ymm2, %ymm2
vpaddd 2560(%esp), %ymm7, %ymm6
vmovdqu %ymm0, 2976(%esp)
vpor %ymm2, %ymm5, %ymm2
vpaddd 2592(%esp), %ymm4, %ymm5
vpxor 2720(%esp), %ymm6, %ymm4
vpaddd 2752(%esp), %ymm0, %ymm0
vmovdqu %ymm6, 3008(%esp)
vmovdqu %ymm5, 3040(%esp)
vpxor 2624(%esp), %ymm5, %ymm6
vpsrld $20, %ymm4, %ymm5
vpslld $12, %ymm4, %ymm4
vmovdqu %ymm0, 1824(%esp)
vpxor %ymm0, %ymm1, %ymm0
vpor %ymm4, %ymm5, %ymm5
vpsrld $20, %ymm6, %ymm4
vpslld $12, %ymm6, %ymm6
vmovdqu 1536(%esp), %ymm1
vmovdqu %ymm5, 3072(%esp)
vpor %ymm6, %ymm4, %ymm6
vpaddd 2784(%esp), %ymm2, %ymm4
vpaddd 2816(%esp), %ymm5, %ymm5
vpshufb %ymm1, %ymm0, %ymm0
vpxor %ymm4, %ymm3, %ymm3
vpxor %ymm5, %ymm7, %ymm7
vmovdqu %ymm4, 1856(%esp)
vmovdqu %ymm0, 1600(%esp)
vmovdqu %ymm5, 1888(%esp)
vpaddd 2848(%esp), %ymm6, %ymm4
vpaddd 2912(%esp), %ymm0, %ymm0
vpshufb %ymm1, %ymm3, %ymm3
vpshufb %ymm1, %ymm7, %ymm5
vpxor 2880(%esp), %ymm4, %ymm7
vmovdqu %ymm3, 1664(%esp)
vmovdqu %ymm4, 1920(%esp)
vmovdqu %ymm0, 1728(%esp)
vpaddd 2944(%esp), %ymm3, %ymm3
vpxor 2976(%esp), %ymm0, %ymm4
vpshufb %ymm1, %ymm7, %ymm1
vpxor %ymm3, %ymm2, %ymm2
vpsrld $25, %ymm4, %ymm7
vpslld $7, %ymm4, %ymm0
vmovdqu %ymm1, 1632(%esp)
vmovdqu %ymm3, 1696(%esp)
vpsrld $25, %ymm2, %ymm4
vpslld $7, %ymm2, %ymm2
vpor %ymm0, %ymm7, %ymm3
vpaddd 3040(%esp), %ymm1, %ymm1
vpor %ymm2, %ymm4, %ymm2
vmovdqu %ymm3, 1792(%esp)
vpxor %ymm1, %ymm6, %ymm7
vmovdqu %ymm2, 1760(%esp)
vpaddd 3008(%esp), %ymm5, %ymm2
vpsrld $25, %ymm7, %ymm3
vpslld $7, %ymm7, %ymm4
vpxor 3072(%esp), %ymm2, %ymm0
vpsrld $25, %ymm0, %ymm6
vpslld $7, %ymm0, %ymm0
vpor %ymm0, %ymm6, %ymm6
vpor %ymm4, %ymm3, %ymm0
addl $-2, %edx
jne chacha_blocks_avx2_5
chacha_blocks_avx2_6:
vmovdqu %ymm2, 1248(%esp)
vmovdqu 1824(%esp), %ymm2
vmovdqu 1856(%esp), %ymm4
vmovdqu %ymm5, 1184(%esp)
vmovdqu %ymm1, 1216(%esp)
vmovdqu 1888(%esp), %ymm5
vmovdqu 1920(%esp), %ymm1
vmovdqu 1792(%esp), %ymm7
vpaddd 896(%esp), %ymm2, %ymm3
vpaddd 928(%esp), %ymm4, %ymm2
vpaddd 1088(%esp), %ymm6, %ymm6
vpaddd 960(%esp), %ymm5, %ymm4
vpaddd 992(%esp), %ymm1, %ymm5
vpaddd 1056(%esp), %ymm7, %ymm1
vpaddd 1024(%esp), %ymm0, %ymm0
vmovdqu %ymm6, 1312(%esp)
vmovdqu 1760(%esp), %ymm7
vpunpckldq %ymm2, %ymm3, %ymm6
vpunpckhdq %ymm2, %ymm3, %ymm3
vmovdqu 1312(%esp), %ymm2
vpaddd 864(%esp), %ymm7, %ymm7
vmovdqu %ymm6, 1344(%esp)
vpunpckldq %ymm5, %ymm4, %ymm6
vpunpckhdq %ymm5, %ymm4, %ymm4
vpunpckldq %ymm1, %ymm0, %ymm5
vpunpckhdq %ymm1, %ymm0, %ymm0
vpunpckhdq %ymm2, %ymm7, %ymm1
vmovdqu %ymm4, 1376(%esp)
vpunpckldq %ymm2, %ymm7, %ymm4
vmovdqu 1344(%esp), %ymm2
vpunpcklqdq %ymm6, %ymm2, %ymm7
vpunpckhqdq %ymm6, %ymm2, %ymm6
vmovdqu 1376(%esp), %ymm2
vmovdqu %ymm7, 1408(%esp)
vpunpcklqdq %ymm4, %ymm5, %ymm7
vpunpckhqdq %ymm4, %ymm5, %ymm4
vpunpcklqdq %ymm2, %ymm3, %ymm5
vpunpckhqdq %ymm2, %ymm3, %ymm3
vmovdqu %ymm5, 1440(%esp)
vpunpcklqdq %ymm1, %ymm0, %ymm5
vpunpckhqdq %ymm1, %ymm0, %ymm1
vmovdqu 1408(%esp), %ymm0
vperm2i128 $32, %ymm7, %ymm0, %ymm2
vmovdqu %ymm2, 1280(%esp)
vperm2i128 $32, %ymm4, %ymm6, %ymm2
vperm2i128 $49, %ymm7, %ymm0, %ymm0
vperm2i128 $49, %ymm4, %ymm6, %ymm7
vmovdqu 1440(%esp), %ymm4
vperm2i128 $32, %ymm5, %ymm4, %ymm6
vmovdqu %ymm6, 1472(%esp)
vperm2i128 $32, %ymm1, %ymm3, %ymm6
vperm2i128 $49, %ymm5, %ymm4, %ymm4
vperm2i128 $49, %ymm1, %ymm3, %ymm1
vmovdqu 1472(%esp), %ymm5
testl %edi, %edi
je chacha_blocks_avx2_51
chacha_blocks_avx2_7:
vmovdqu 1280(%esp), %ymm3
vpxor 448(%edi), %ymm1, %ymm1
vpxor 384(%edi), %ymm4, %ymm4
vpxor 320(%edi), %ymm7, %ymm7
vpxor 256(%edi), %ymm0, %ymm0
vpxor 192(%edi), %ymm6, %ymm6
vpxor 128(%edi), %ymm5, %ymm5
vpxor 64(%edi), %ymm2, %ymm2
vpxor (%edi), %ymm3, %ymm3
vmovdqu %ymm1, 448(%ebx)
vmovdqu 1184(%esp), %ymm1
vmovdqu %ymm2, 64(%ebx)
vmovdqu %ymm3, (%ebx)
vmovdqu %ymm0, 256(%ebx)
vmovdqu 1248(%esp), %ymm0
vmovdqu 1216(%esp), %ymm2
vmovdqu %ymm5, 128(%ebx)
vmovdqu %ymm7, 320(%ebx)
vmovdqu %ymm6, 192(%ebx)
vmovdqu 1728(%esp), %ymm6
vmovdqu %ymm4, 384(%ebx)
vpaddd 1120(%esp), %ymm1, %ymm3
vpaddd 832(%esp), %ymm0, %ymm5
vpaddd 800(%esp), %ymm2, %ymm7
vpaddd 768(%esp), %ymm6, %ymm6
vmovdqu 1600(%esp), %ymm1
vmovdqu 1696(%esp), %ymm0
vmovdqu 1664(%esp), %ymm2
vpaddd 672(%esp), %ymm1, %ymm1
vpaddd 736(%esp), %ymm0, %ymm4
vpaddd 1152(%esp), %ymm2, %ymm0
vmovdqu 1632(%esp), %ymm2
vmovdqu %ymm1, 224(%esp)
vpunpckldq %ymm7, %ymm5, %ymm1
vpunpckhdq %ymm7, %ymm5, %ymm7
vmovdqu 224(%esp), %ymm5
vpaddd 704(%esp), %ymm2, %ymm2
vmovdqu %ymm1, 320(%esp)
vpunpckldq %ymm4, %ymm6, %ymm1
vpunpckhdq %ymm4, %ymm6, %ymm4
vpunpckldq %ymm5, %ymm2, %ymm6
vmovdqu %ymm4, 352(%esp)
vpunpckldq %ymm3, %ymm0, %ymm4
vpunpckhdq %ymm3, %ymm0, %ymm0
vpunpckhdq %ymm5, %ymm2, %ymm3
vmovdqu 320(%esp), %ymm5
vpunpcklqdq %ymm1, %ymm5, %ymm2
vpunpckhqdq %ymm1, %ymm5, %ymm1
vmovdqu 352(%esp), %ymm5
vmovdqu %ymm2, 384(%esp)
vpunpcklqdq %ymm6, %ymm4, %ymm2
vpunpckhqdq %ymm6, %ymm4, %ymm4
vpunpcklqdq %ymm5, %ymm7, %ymm6
vpunpckhqdq %ymm5, %ymm7, %ymm7
vpunpckhqdq %ymm3, %ymm0, %ymm5
vmovdqu %ymm6, 416(%esp)
vpunpcklqdq %ymm3, %ymm0, %ymm6
vmovdqu 384(%esp), %ymm3
vperm2i128 $32, %ymm2, %ymm3, %ymm0
vpxor 32(%edi), %ymm0, %ymm0
vmovdqu %ymm0, 448(%esp)
vperm2i128 $32, %ymm4, %ymm1, %ymm0
vpxor 96(%edi), %ymm0, %ymm0
vmovdqu %ymm0, 480(%esp)
vperm2i128 $2, 416(%esp), %ymm6, %ymm0
vpxor 160(%edi), %ymm0, %ymm0
vmovdqu %ymm0, 512(%esp)
vperm2i128 $32, %ymm5, %ymm7, %ymm0
vperm2i128 $49, %ymm5, %ymm7, %ymm5
vmovdqu 448(%esp), %ymm7
vpxor 224(%edi), %ymm0, %ymm0
vpxor 480(%edi), %ymm5, %ymm5
vperm2i128 $49, %ymm2, %ymm3, %ymm3
vperm2i128 $49, %ymm4, %ymm1, %ymm4
vperm2i128 $19, 416(%esp), %ymm6, %ymm1
vpxor 288(%edi), %ymm3, %ymm2
vpxor 352(%edi), %ymm4, %ymm4
vpxor 416(%edi), %ymm1, %ymm1
vmovdqu %ymm7, 32(%ebx)
vmovdqu 480(%esp), %ymm7
vmovdqu 512(%esp), %ymm3
vmovdqu %ymm0, 224(%ebx)
vmovdqu %ymm2, 288(%ebx)
vmovdqu %ymm4, 352(%ebx)
vmovdqu %ymm7, 96(%ebx)
vmovdqu %ymm3, 160(%ebx)
vmovdqu %ymm1, 416(%ebx)
vmovdqu %ymm5, 480(%ebx)
addl $512, %edi
chacha_blocks_avx2_8:
movl 1512(%esp), %edx
addl $512, %ebx
addl $-512, %edx
movl %edx, 1512(%esp)
cmpl $512, %edx
jae chacha_blocks_avx2_4
chacha_blocks_avx2_9:
movl 1504(%esp), %esi
vmovdqu 304(%esp), %xmm0
chacha_blocks_avx2_10:
cmpl $256, %edx
jb chacha_blocks_avx2_18
chacha_blocks_avx2_11:
movl $2, %eax
vpxor %ymm3, %ymm3, %ymm3
vinserti128 $1, %xmm0, %ymm0, %ymm5
vinserti128 $1, 592(%esp), %ymm3, %ymm7
vpaddq %ymm7, %ymm5, %ymm0
vmovd %eax, %xmm7
vmovdqu %ymm0, (%esp)
vbroadcasti128 560(%esp), %ymm1
vbroadcasti128 576(%esp), %ymm6
vinserti128 $1, %xmm7, %ymm7, %ymm5
vmovdqu %ymm1, 224(%esp)
vmovdqu %ymm1, 192(%esp)
vmovdqu %ymm6, 160(%esp)
vmovdqu %ymm1, 32(%esp)
vmovdqu %ymm6, 128(%esp)
vmovdqu 224(%esp), %ymm1
vpaddq %ymm5, %ymm0, %ymm7
vbroadcasti128 544(%esp), %ymm2
vmovdqa %ymm2, %ymm4
vmovdqu %ymm2, 320(%esp)
vmovdqu %ymm2, 64(%esp)
vmovdqu %ymm7, 96(%esp)
vmovdqu %ymm7, 352(%esp)
vmovdqu %ymm4, 384(%esp)
vmovdqu 192(%esp), %ymm2
movl 1516(%esp), %eax
vmovdqa %ymm0, %ymm3
vmovdqu 160(%esp), %ymm0
chacha_blocks_avx2_12:
vpaddd 384(%esp), %ymm1, %ymm4
vpaddd 320(%esp), %ymm2, %ymm7
vpxor %ymm4, %ymm3, %ymm5
vmovdqu 1568(%esp), %ymm3
vmovdqu %ymm7, 416(%esp)
vpxor 352(%esp), %ymm7, %ymm7
vpshufb %ymm3, %ymm5, %ymm5
vpshufb %ymm3, %ymm7, %ymm3
vpaddd %ymm5, %ymm6, %ymm6
vpaddd %ymm3, %ymm0, %ymm0
vpxor %ymm6, %ymm1, %ymm1
vpxor %ymm0, %ymm2, %ymm7
vpsrld $20, %ymm1, %ymm2
vpslld $12, %ymm1, %ymm1
vpor %ymm1, %ymm2, %ymm1
vpsrld $20, %ymm7, %ymm2
vpslld $12, %ymm7, %ymm7
vpaddd %ymm1, %ymm4, %ymm4
vpor %ymm7, %ymm2, %ymm2
vmovdqu %ymm4, 448(%esp)
vpxor %ymm4, %ymm5, %ymm5
vpaddd 416(%esp), %ymm2, %ymm7
vmovdqu 1536(%esp), %ymm4
vpxor %ymm7, %ymm3, %ymm3
vpshufd $147, %ymm7, %ymm7
vpshufb %ymm4, %ymm5, %ymm5
vpshufb %ymm4, %ymm3, %ymm4
vpaddd %ymm5, %ymm6, %ymm6
vpaddd %ymm4, %ymm0, %ymm3
vpshufd $78, %ymm5, %ymm5
vpshufd $78, %ymm4, %ymm4
vpxor %ymm6, %ymm1, %ymm0
vpxor %ymm3, %ymm2, %ymm2
vpshufd $57, %ymm6, %ymm6
vpshufd $57, %ymm3, %ymm3
vpsrld $25, %ymm0, %ymm1
vpslld $7, %ymm0, %ymm0
vpor %ymm0, %ymm1, %ymm1
vpsrld $25, %ymm2, %ymm0
vpslld $7, %ymm2, %ymm2
vpor %ymm2, %ymm0, %ymm0
vpshufd $147, 448(%esp), %ymm2
vpaddd %ymm0, %ymm7, %ymm7
vpaddd %ymm1, %ymm2, %ymm2
vpxor %ymm7, %ymm4, %ymm4
vmovdqu %ymm2, 480(%esp)
vpxor %ymm2, %ymm5, %ymm2
vmovdqu 1568(%esp), %ymm5
vpshufb %ymm5, %ymm2, %ymm2
vpshufb %ymm5, %ymm4, %ymm4
vpaddd %ymm2, %ymm6, %ymm6
vpaddd %ymm4, %ymm3, %ymm3
vpxor %ymm6, %ymm1, %ymm5
vpxor %ymm3, %ymm0, %ymm1
vpsrld $20, %ymm5, %ymm0
vpslld $12, %ymm5, %ymm5
vpor %ymm5, %ymm0, %ymm0
vpsrld $20, %ymm1, %ymm5
vpslld $12, %ymm1, %ymm1
vpor %ymm1, %ymm5, %ymm1
vpaddd 480(%esp), %ymm0, %ymm5
vmovdqu %ymm1, 512(%esp)
vpaddd %ymm1, %ymm7, %ymm1
vpxor %ymm5, %ymm2, %ymm7
vmovdqu 1536(%esp), %ymm2
vpxor %ymm1, %ymm4, %ymm4
vpshufb %ymm2, %ymm7, %ymm7
vpshufb %ymm2, %ymm4, %ymm4
vpshufd $57, %ymm5, %ymm2
vpaddd %ymm7, %ymm6, %ymm6
vpshufd $57, %ymm1, %ymm5
vpaddd %ymm4, %ymm3, %ymm1
vpshufd $78, %ymm4, %ymm4
vpshufd $78, %ymm7, %ymm3
vpxor %ymm6, %ymm0, %ymm7
vpshufd $147, %ymm1, %ymm0
vpshufd $147, %ymm6, %ymm6
vmovdqu %ymm4, 352(%esp)
vmovdqu %ymm2, 384(%esp)
vmovdqu %ymm5, 320(%esp)
vpxor 512(%esp), %ymm1, %ymm4
vpsrld $25, %ymm7, %ymm1
vpslld $7, %ymm7, %ymm2
vpsrld $25, %ymm4, %ymm5
vpor %ymm2, %ymm1, %ymm1
vpslld $7, %ymm4, %ymm2
vpor %ymm2, %ymm5, %ymm2
addl $-2, %eax
jne chacha_blocks_avx2_12
chacha_blocks_avx2_13:
vmovdqu %ymm0, 160(%esp)
vmovdqu %ymm2, 192(%esp)
vmovdqu %ymm1, 224(%esp)
vmovdqu (%esp), %ymm0
vmovdqu 32(%esp), %ymm1
vmovdqu 384(%esp), %ymm4
vmovdqu 64(%esp), %ymm2
vpaddd 128(%esp), %ymm6, %ymm6
vpaddd 224(%esp), %ymm1, %ymm5
vpaddd %ymm0, %ymm3, %ymm0
vpaddd %ymm2, %ymm4, %ymm4
vperm2i128 $32, %ymm5, %ymm4, %ymm7
vperm2i128 $32, %ymm0, %ymm6, %ymm3
vperm2i128 $49, %ymm5, %ymm4, %ymm4
vperm2i128 $49, %ymm0, %ymm6, %ymm0
testl %edi, %edi
je chacha_blocks_avx2_15
chacha_blocks_avx2_14:
vpxor (%edi), %ymm7, %ymm7
vpxor 32(%edi), %ymm3, %ymm3
vpxor 64(%edi), %ymm4, %ymm4
vpxor 96(%edi), %ymm0, %ymm0
chacha_blocks_avx2_15:
vmovdqu %ymm3, 32(%ebx)
vmovdqu %ymm4, 64(%ebx)
vmovdqu %ymm0, 96(%ebx)
vmovdqu %ymm7, (%ebx)
vpaddd 320(%esp), %ymm2, %ymm0
vpaddd 192(%esp), %ymm1, %ymm3
vmovdqu 128(%esp), %ymm1
vmovdqu 352(%esp), %ymm2
vpaddd 160(%esp), %ymm1, %ymm4
vpaddd 96(%esp), %ymm2, %ymm5
vperm2i128 $32, %ymm3, %ymm0, %ymm1
vperm2i128 $32, %ymm5, %ymm4, %ymm2
vperm2i128 $49, %ymm3, %ymm0, %ymm0
vperm2i128 $49, %ymm5, %ymm4, %ymm3
je chacha_blocks_avx2_17
chacha_blocks_avx2_16:
vpxor 128(%edi), %ymm1, %ymm1
vpxor 160(%edi), %ymm2, %ymm2
vpxor 192(%edi), %ymm0, %ymm0
vpxor 224(%edi), %ymm3, %ymm3
addl $256, %edi
chacha_blocks_avx2_17:
addl $4, 304(%esp)
vmovdqu %ymm0, 192(%ebx)
vmovdqu %ymm1, 128(%ebx)
vmovdqu %ymm2, 160(%ebx)
vmovdqu %ymm3, 224(%ebx)
adcl $0, 308(%esp)
addl $-256, %edx
vmovdqu 304(%esp), %xmm0
addl $256, %ebx
chacha_blocks_avx2_18:
cmpl $128, %edx
jb chacha_blocks_avx2_24
chacha_blocks_avx2_19:
vpxor %ymm7, %ymm7, %ymm7
vinserti128 $1, %xmm0, %ymm0, %ymm0
vinserti128 $1, 592(%esp), %ymm7, %ymm7
vpaddq %ymm7, %ymm0, %ymm7
vbroadcasti128 560(%esp), %ymm3
vbroadcasti128 576(%esp), %ymm2
vbroadcasti128 544(%esp), %ymm6
vmovdqu %ymm2, 32(%esp)
vmovdqu %ymm3, 64(%esp)
vmovdqu %ymm7, (%esp)
vmovdqu %ymm6, 96(%esp)
vmovdqa %ymm6, %ymm1
vmovdqa %ymm3, %ymm5
vmovdqa %ymm2, %ymm4
vmovdqa %ymm7, %ymm0
movl 1516(%esp), %eax
vmovdqu 1536(%esp), %ymm2
vmovdqu 1568(%esp), %ymm3
chacha_blocks_avx2_20:
vpaddd %ymm5, %ymm1, %ymm6
vpxor %ymm6, %ymm0, %ymm1
vpshufb %ymm3, %ymm1, %ymm0
vpaddd %ymm0, %ymm4, %ymm1
vpxor %ymm1, %ymm5, %ymm4
vpsrld $20, %ymm4, %ymm5
vpslld $12, %ymm4, %ymm7
vpor %ymm7, %ymm5, %ymm7
vpaddd %ymm7, %ymm6, %ymm5
vpxor %ymm5, %ymm0, %ymm0
vpshufd $147, %ymm5, %ymm5
vpshufb %ymm2, %ymm0, %ymm4
vpaddd %ymm4, %ymm1, %ymm6
vpshufd $78, %ymm4, %ymm4
vpxor %ymm6, %ymm7, %ymm1
vpshufd $57, %ymm6, %ymm6
vpsrld $25, %ymm1, %ymm0
vpslld $7, %ymm1, %ymm7
vpor %ymm7, %ymm0, %ymm0
vpaddd %ymm0, %ymm5, %ymm1
vpxor %ymm1, %ymm4, %ymm4
vpshufb %ymm3, %ymm4, %ymm7
vpaddd %ymm7, %ymm6, %ymm5
vpxor %ymm5, %ymm0, %ymm4
vpsrld $20, %ymm4, %ymm0
vpslld $12, %ymm4, %ymm6
vpor %ymm6, %ymm0, %ymm4
vpaddd %ymm4, %ymm1, %ymm0
vpxor %ymm0, %ymm7, %ymm1
vpshufb %ymm2, %ymm1, %ymm7
vpshufd $57, %ymm0, %ymm1
vpaddd %ymm7, %ymm5, %ymm5
vpshufd $78, %ymm7, %ymm0
vpxor %ymm5, %ymm4, %ymm6
vpshufd $147, %ymm5, %ymm4
vpsrld $25, %ymm6, %ymm5
vpslld $7, %ymm6, %ymm7
vpor %ymm7, %ymm5, %ymm5
addl $-2, %eax
jne chacha_blocks_avx2_20
chacha_blocks_avx2_21:
vmovdqu (%esp), %ymm7
vmovdqu 32(%esp), %ymm2
vmovdqu 64(%esp), %ymm3
vmovdqu 96(%esp), %ymm6
vpaddd %ymm7, %ymm0, %ymm0
vpaddd %ymm2, %ymm4, %ymm2
vpaddd %ymm3, %ymm5, %ymm3
vpaddd %ymm6, %ymm1, %ymm1
vperm2i128 $32, %ymm3, %ymm1, %ymm4
vperm2i128 $32, %ymm0, %ymm2, %ymm5
vperm2i128 $49, %ymm3, %ymm1, %ymm1
vperm2i128 $49, %ymm0, %ymm2, %ymm0
testl %edi, %edi
je chacha_blocks_avx2_23
chacha_blocks_avx2_22:
vpxor (%edi), %ymm4, %ymm4
vpxor 32(%edi), %ymm5, %ymm5
vpxor 64(%edi), %ymm1, %ymm1
vpxor 96(%edi), %ymm0, %ymm0
addl $128, %edi
chacha_blocks_avx2_23:
addl $2, 304(%esp)
vmovdqu %ymm0, 96(%ebx)
vmovdqu %ymm4, (%ebx)
vmovdqu %ymm5, 32(%ebx)
vmovdqu %ymm1, 64(%ebx)
adcl $0, 308(%esp)
addl $-128, %edx
vmovdqu 304(%esp), %xmm0
addl $128, %ebx
chacha_blocks_avx2_24:
testl %edx, %edx
jne chacha_blocks_avx2_26
chacha_blocks_avx2_25:
movl 8(%ebp), %ecx
movl 304(%esp), %eax
movl 308(%esp), %edx
movl %eax, 32(%ecx)
movl %edx, 36(%ecx)
vzeroupper
addl $3124, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx2_26:
vmovdqu 1568(%esp), %ymm1
vmovdqu 1536(%esp), %ymm2
vmovdqu 576(%esp), %xmm7
vmovdqu 544(%esp), %xmm6
movl 304(%esp), %esi
movl 308(%esp), %ecx
vmovups %xmm1, 16(%esp)
vmovups %xmm2, (%esp)
vmovdqu 560(%esp), %xmm1
jmp chacha_blocks_avx2_27
chacha_blocks_avx2_43:
addl $-64, %edx
addl $64, %ebx
chacha_blocks_avx2_27:
cmpl $64, %edx
jae chacha_blocks_avx2_38
chacha_blocks_avx2_28:
testl %edi, %edi
je chacha_blocks_avx2_37
chacha_blocks_avx2_29:
testl %edx, %edx
jbe chacha_blocks_avx2_36
chacha_blocks_avx2_30:
movl %edx, %eax
shrl $1, %eax
movl %eax, 60(%esp)
testl %eax, %eax
jbe chacha_blocks_avx2_45
chacha_blocks_avx2_31:
movl %esi, 52(%esp)
xorl %eax, %eax
movl %edx, 1512(%esp)
movl %ebx, 56(%esp)
movl 60(%esp), %esi
chacha_blocks_avx2_32:
movzbl (%edi,%eax,2), %edx
movb %dl, 64(%esp,%eax,2)
movzbl 1(%edi,%eax,2), %ebx
movb %bl, 65(%esp,%eax,2)
incl %eax
cmpl %esi, %eax
jb chacha_blocks_avx2_32
chacha_blocks_avx2_33:
movl 52(%esp), %esi
lea 1(%eax,%eax), %eax
movl 1512(%esp), %edx
movl 56(%esp), %ebx
movl %eax, 48(%esp)
chacha_blocks_avx2_34:
lea -1(%eax), %eax
cmpl %edx, %eax
jae chacha_blocks_avx2_36
chacha_blocks_avx2_35:
movzbl (%eax,%edi), %eax
movl 48(%esp), %edi
movb %al, 63(%esp,%edi)
chacha_blocks_avx2_36:
lea 64(%esp), %edi
chacha_blocks_avx2_37:
movl %ebx, 1508(%esp)
lea 64(%esp), %ebx
chacha_blocks_avx2_38:
vmovdqu %xmm0, 32(%esp)
vmovdqa %xmm6, %xmm2
movl 1516(%esp), %eax
vmovdqa %xmm1, %xmm3
vmovups 16(%esp), %xmm1
vmovdqa %xmm7, %xmm4
vmovdqa %xmm0, %xmm5
vmovups (%esp), %xmm0
chacha_blocks_avx2_39:
vpaddd %xmm3, %xmm2, %xmm6
vpxor %xmm6, %xmm5, %xmm2
vpshufb %xmm1, %xmm2, %xmm5
vpaddd %xmm5, %xmm4, %xmm2
vpxor %xmm2, %xmm3, %xmm4
vpsrld $20, %xmm4, %xmm3
vpslld $12, %xmm4, %xmm7
vpxor %xmm7, %xmm3, %xmm7
vpaddd %xmm7, %xmm6, %xmm3
vpxor %xmm3, %xmm5, %xmm5
vpshufb %xmm0, %xmm5, %xmm4
vpaddd %xmm4, %xmm2, %xmm6
vpxor %xmm6, %xmm7, %xmm2
vpsrld $25, %xmm2, %xmm5
vpslld $7, %xmm2, %xmm7
vpshufd $147, %xmm3, %xmm3
vpxor %xmm7, %xmm5, %xmm5
vpshufd $78, %xmm4, %xmm4
vpaddd %xmm5, %xmm3, %xmm2
vpxor %xmm2, %xmm4, %xmm4
vpshufb %xmm1, %xmm4, %xmm7
vpshufd $57, %xmm6, %xmm6
vpaddd %xmm7, %xmm6, %xmm3
vpxor %xmm3, %xmm5, %xmm4
vpsrld $20, %xmm4, %xmm5
vpslld $12, %xmm4, %xmm6
vpxor %xmm6, %xmm5, %xmm4
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
vpxor %xmm7, %xmm3, %xmm3
addl $-2, %eax
jne chacha_blocks_avx2_39
chacha_blocks_avx2_40:
vmovdqu 576(%esp), %xmm7
vmovdqu 560(%esp), %xmm1
vpaddd %xmm7, %xmm4, %xmm4
vmovdqu 544(%esp), %xmm6
vpaddd %xmm1, %xmm3, %xmm3
vmovdqu 32(%esp), %xmm0
vpaddd %xmm6, %xmm2, %xmm2
vpaddd %xmm0, %xmm5, %xmm5
testl %edi, %edi
je chacha_blocks_avx2_42
chacha_blocks_avx2_41:
vpxor (%edi), %xmm2, %xmm2
vpxor 16(%edi), %xmm3, %xmm3
vpxor 32(%edi), %xmm4, %xmm4
vpxor 48(%edi), %xmm5, %xmm5
addl $64, %edi
chacha_blocks_avx2_42:
addl $1, %esi
vmovdqu %xmm2, (%ebx)
vmovdqu %xmm3, 16(%ebx)
vmovdqu %xmm4, 32(%ebx)
vmovdqu %xmm5, 48(%ebx)
vpaddq 592(%esp), %xmm0, %xmm0
adcl $0, %ecx
cmpl $64, %edx
jbe chacha_blocks_avx2_46
jmp chacha_blocks_avx2_43
chacha_blocks_avx2_44:
vzeroupper
addl $3124, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx2_45:
movl $1, %eax
movl %eax, 48(%esp)
jmp chacha_blocks_avx2_34
chacha_blocks_avx2_46:
movl %esi, 304(%esp)
movl %ecx, 308(%esp)
jae chacha_blocks_avx2_25
chacha_blocks_avx2_47:
testl %edx, %edx
jbe chacha_blocks_avx2_25
chacha_blocks_avx2_48:
movl 1508(%esp), %esi
xorl %ecx, %ecx
chacha_blocks_avx2_49:
movzbl (%ecx,%ebx), %eax
movb %al, (%ecx,%esi)
incl %ecx
cmpl %edx, %ecx
jb chacha_blocks_avx2_49
jmp chacha_blocks_avx2_25
chacha_blocks_avx2_51:
vmovdqu %ymm0, 256(%ebx)
vmovdqu 1248(%esp), %ymm0
vmovdqu %ymm6, 192(%ebx)
vmovdqu %ymm7, 320(%ebx)
vmovdqu 1280(%esp), %ymm3
vmovdqu 1216(%esp), %ymm6
vmovdqu %ymm4, 384(%ebx)
vmovdqu %ymm1, 448(%ebx)
vmovdqu 1696(%esp), %ymm4
vmovdqu %ymm3, (%ebx)
vmovdqu %ymm2, 64(%ebx)
vmovdqu %ymm5, 128(%ebx)
vmovdqu 1728(%esp), %ymm5
vpaddd 832(%esp), %ymm0, %ymm7
vpaddd 800(%esp), %ymm6, %ymm1
vpaddd 736(%esp), %ymm4, %ymm2
vpaddd 768(%esp), %ymm5, %ymm5
vmovdqu 1664(%esp), %ymm0
vmovdqu 1184(%esp), %ymm6
vpaddd 1152(%esp), %ymm0, %ymm3
vpaddd 1120(%esp), %ymm6, %ymm4
vmovdqu 1632(%esp), %ymm0
vpaddd 704(%esp), %ymm0, %ymm6
vmovdqu 1600(%esp), %ymm0
vpaddd 672(%esp), %ymm0, %ymm0
vmovdqu %ymm0, (%esp)
vpunpckldq %ymm1, %ymm7, %ymm0
vpunpckhdq %ymm1, %ymm7, %ymm1
vmovdqu (%esp), %ymm7
vmovdqu %ymm0, 32(%esp)
vpunpckldq %ymm2, %ymm5, %ymm0
vpunpckhdq %ymm2, %ymm5, %ymm2
vpunpckldq %ymm7, %ymm6, %ymm5
vpunpckhdq %ymm7, %ymm6, %ymm6
vmovdqu %ymm2, 64(%esp)
vpunpckldq %ymm4, %ymm3, %ymm2
vpunpckhdq %ymm4, %ymm3, %ymm4
vmovdqu 32(%esp), %ymm3
vpunpcklqdq %ymm0, %ymm3, %ymm7
vpunpckhqdq %ymm0, %ymm3, %ymm3
vpunpckhqdq %ymm5, %ymm2, %ymm0
vmovdqu %ymm7, 96(%esp)
vpunpcklqdq %ymm5, %ymm2, %ymm7
vmovdqu 64(%esp), %ymm5
vpunpcklqdq %ymm5, %ymm1, %ymm2
vpunpckhqdq %ymm5, %ymm1, %ymm1
vmovdqu 96(%esp), %ymm5
vmovdqu %ymm2, 128(%esp)
vpunpcklqdq %ymm6, %ymm4, %ymm2
vpunpckhqdq %ymm6, %ymm4, %ymm4
vperm2i128 $32, %ymm7, %ymm5, %ymm6
vmovdqu %ymm6, 160(%esp)
vperm2i128 $32, %ymm0, %ymm3, %ymm6
vperm2i128 $49, %ymm0, %ymm3, %ymm3
vmovdqu 128(%esp), %ymm0
vmovdqu %ymm3, 192(%esp)
vmovdqu %ymm6, 96(%ebx)
vperm2i128 $49, %ymm7, %ymm5, %ymm7
vperm2i128 $32, %ymm2, %ymm0, %ymm3
vperm2i128 $32, %ymm4, %ymm1, %ymm5
vperm2i128 $49, %ymm2, %ymm0, %ymm0
vperm2i128 $49, %ymm4, %ymm1, %ymm2
vmovdqu 160(%esp), %ymm1
vmovdqu %ymm3, 160(%ebx)
vmovdqu %ymm5, 224(%ebx)
vmovdqu %ymm7, 288(%ebx)
vmovdqu %ymm0, 416(%ebx)
vmovdqu %ymm1, 32(%ebx)
vmovdqu 192(%esp), %ymm1
vmovdqu %ymm2, 480(%ebx)
vmovdqu %ymm1, 352(%ebx)
jmp chacha_blocks_avx2_8
FN_END chacha_blocks_avx2


GLOBAL_HIDDEN_FN hchacha_avx2
hchacha_avx2_local:
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
hchacha_avx2_mainloop:
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
jne hchacha_avx2_mainloop
vmovdqu %xmm0, (%edx)
vmovdqu %xmm3, 16(%edx)
ret
FN_END hchacha_avx2

GLOBAL_HIDDEN_FN chacha_avx2
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
call chacha_blocks_avx2_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm0, 16(%ebx)
vmovdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END chacha_avx2

GLOBAL_HIDDEN_FN xchacha_avx2
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
call hchacha_avx2_local
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
call chacha_blocks_avx2_local
vpxor %xmm0, %xmm0, %xmm0
vmovdqa %xmm0, 0(%ebx)
vmovdqa %xmm0, 16(%ebx)
vmovdqa %xmm0, 32(%ebx)
movl %ebp, %esp
popl %ebx
popl %ebp
ret
FN_END xchacha_avx2

INCLUDE_VAR_FILE "chacha/chacha_constants_x86.inc", chacha_constants

