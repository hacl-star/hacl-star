#include "x86.inc"

SECTION_TEXT

GLOBAL_HIDDEN_FN chacha_blocks_avx2
chacha_blocks_avx2_local:
pushl %ebp
movl %esp, %ebp
andl $-64, %esp
pushl %esi
pushl %edi
pushl %ebx
subl $3828, %esp
pushl $1
popl %ecx
movl 8(%ebp), %ebx
movl 12(%ebp), %eax
movl %eax, 2156(%esp)
movl 16(%ebp), %eax
vmovd %ecx, %xmm2
LOAD_VAR_PIC chacha_constants, %edx
vmovdqu 0(%edx), %xmm3
vmovdqu 16(%edx), %xmm0
vmovdqu 32(%edx), %xmm1
movl 48(%ebx), %ecx
movl 20(%ebp), %edx
vmovdqu %xmm0, 2160(%esp)
vmovdqu %xmm1, 2176(%esp)
vmovdqu %xmm2, 2080(%esp)
movl %eax, 2144(%esp)
movl %ecx, 2148(%esp)
xorl %ecx, %ecx
vmovdqu %xmm3, 512(%esp)
chacha_blocks_avx2_2:
vmovdqu (%ebx,%ecx,4), %xmm0
vmovdqu %xmm0, 528(%esp,%ecx,4)
addl $4, %ecx
cmpl $12, %ecx
jb chacha_blocks_avx2_2
chacha_blocks_avx2_3:
vmovdqu 512(%esp), %xmm0
vmovdqu 528(%esp), %xmm1
vmovdqu 544(%esp), %xmm2
vmovdqu %xmm0, 2096(%esp)
vmovdqu %xmm1, 2112(%esp)
vmovdqu %xmm2, 2128(%esp)
cmpl $512, %edx
jb chacha_blocks_avx2_11
chacha_blocks_avx2_4:
vpbroadcastd 536(%esp), %ymm7
vmovdqu %ymm7, 2048(%esp)
vpbroadcastd 540(%esp), %ymm7
vmovdqu %ymm7, 2016(%esp)
vpbroadcastd 568(%esp), %ymm7
vmovdqu %ymm7, 1856(%esp)
vpbroadcastd 572(%esp), %ymm7
vmovdqu %ymm7, 1824(%esp)
vpbroadcastd 548(%esp), %ymm7
vmovdqu %ymm7, 1952(%esp)
vbroadcasti128 2160(%esp), %ymm4
vpbroadcastd 2128(%esp), %ymm0
vpbroadcastd 552(%esp), %ymm7
vmovdqu %ymm4, 2592(%esp)
vmovdqu %ymm0, 1984(%esp)
vmovdqu %ymm7, 1920(%esp)
vbroadcasti128 2176(%esp), %ymm6
vpbroadcastd 2096(%esp), %ymm5
vpbroadcastd 2112(%esp), %ymm4
vpbroadcastd 516(%esp), %ymm3
vpbroadcastd 520(%esp), %ymm2
vpbroadcastd 524(%esp), %ymm1
vpbroadcastd 532(%esp), %ymm0
vpbroadcastd 556(%esp), %ymm7
movl %edx, 2152(%esp)
movl 560(%esp), %ecx
movl 564(%esp), %ebx
movl 2156(%esp), %edx
vmovdqu %ymm7, 1888(%esp)
vmovdqu %ymm0, 1600(%esp)
vmovdqu %ymm4, 1568(%esp)
vmovdqu %ymm1, 1536(%esp)
vmovdqu %ymm2, 1504(%esp)
vmovdqu %ymm3, 1472(%esp)
vmovdqu %ymm5, 1440(%esp)
vmovdqu %ymm6, 2208(%esp)
jmp chacha_blocks_avx2_5
.p2align 6,,63
chacha_blocks_avx2_5:
movl %ecx, %esi
movl %ebx, %edi
addl $1, %esi
movl %esi, 1380(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $2, %esi
movl %edi, 1412(%esp)
movl %ebx, %edi
movl %esi, 1384(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $3, %esi
movl %edi, 1416(%esp)
movl %ebx, %edi
movl %esi, 1388(%esp)
movl %ecx, %esi
vmovdqu 1920(%esp), %ymm4
adcl $0, %edi
vmovdqu 1536(%esp), %ymm5
vmovdqu 1600(%esp), %ymm0
vmovdqu 2048(%esp), %ymm1
vmovdqu 1472(%esp), %ymm7
vmovdqu %ymm4, 2368(%esp)
vmovdqu 1888(%esp), %ymm4
vmovdqu %ymm5, 2464(%esp)
vmovdqu %ymm0, 2432(%esp)
vmovdqu %ymm1, 2400(%esp)
vmovdqu 1568(%esp), %ymm5
vmovdqu %ymm4, 2336(%esp)
vmovdqu 1856(%esp), %ymm4
vmovdqu 2016(%esp), %ymm2
vmovdqu 1984(%esp), %ymm1
vmovdqu %ymm7, 2528(%esp)
vmovdqu 1952(%esp), %ymm0
vmovdqu %ymm4, 2272(%esp)
vmovdqu 1824(%esp), %ymm4
addl $4, %esi
movl %edi, 1420(%esp)
movl %ebx, %edi
movl %esi, 1392(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $5, %esi
movl %edi, 1424(%esp)
movl %ebx, %edi
movl %esi, 1396(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $6, %esi
movl %edi, 1428(%esp)
movl %ebx, %edi
movl %esi, 1400(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $7, %esi
movl %edi, 1432(%esp)
movl %ebx, %edi
adcl $0, %edi
movl %ebx, 1408(%esp)
movl %edi, 1436(%esp)
movl %ecx, 1376(%esp)
addl $8, %ecx
movl %esi, 1404(%esp)
vmovdqu 1408(%esp), %ymm6
adcl $0, %ebx
vmovdqu 1376(%esp), %ymm3
vmovdqu %ymm4, 2240(%esp)
vmovdqu %ymm6, 1632(%esp)
vmovdqu %ymm6, 1696(%esp)
vmovdqu %ymm3, 1664(%esp)
vmovdqu %ymm3, 2304(%esp)
vmovdqu 1504(%esp), %ymm6
vmovdqu 1440(%esp), %ymm3
vmovdqu %ymm6, 2560(%esp)
vmovdqu %ymm3, 2496(%esp)
vmovdqu 1696(%esp), %ymm6
movl 2148(%esp), %esi
movl %ecx, 560(%esp)
movl %ebx, 564(%esp)
chacha_blocks_avx2_6:
vmovdqu 2432(%esp), %ymm7
vmovdqu %ymm2, 2624(%esp)
vpaddd 2496(%esp), %ymm5, %ymm3
vpaddd 2464(%esp), %ymm2, %ymm2
vpaddd 2528(%esp), %ymm7, %ymm7
vpxor 2304(%esp), %ymm3, %ymm4
vmovdqu %ymm3, 2656(%esp)
vmovdqu 2592(%esp), %ymm3
vmovdqu %ymm7, 2688(%esp)
vmovdqu %ymm2, 2752(%esp)
vpxor %ymm7, %ymm6, %ymm6
vpxor 2240(%esp), %ymm2, %ymm2
vmovdqu 2400(%esp), %ymm7
vpshufb %ymm3, %ymm4, %ymm4
vpshufb %ymm3, %ymm6, %ymm6
vpshufb %ymm3, %ymm2, %ymm2
vpaddd 2560(%esp), %ymm7, %ymm7
vpaddd %ymm4, %ymm1, %ymm1
vpaddd %ymm6, %ymm0, %ymm0
vmovdqu %ymm2, 2784(%esp)
vmovdqu %ymm7, 2720(%esp)
vmovdqu %ymm1, 2816(%esp)
vmovdqu %ymm0, 2848(%esp)
vpxor 2272(%esp), %ymm7, %ymm7
vpxor %ymm1, %ymm5, %ymm5
vpxor 2432(%esp), %ymm0, %ymm0
vpshufb %ymm3, %ymm7, %ymm7
vpsrld $20, %ymm5, %ymm1
vpslld $12, %ymm5, %ymm3
vpxor %ymm3, %ymm1, %ymm5
vpsrld $20, %ymm0, %ymm1
vpslld $12, %ymm0, %ymm0
vpaddd 2336(%esp), %ymm2, %ymm3
vmovdqu %ymm5, 2880(%esp)
vpxor %ymm0, %ymm1, %ymm1
vpaddd 2368(%esp), %ymm7, %ymm0
vmovdqu %ymm3, 2944(%esp)
vpxor 2400(%esp), %ymm0, %ymm2
vmovdqu %ymm0, 2912(%esp)
vpxor 2624(%esp), %ymm3, %ymm0
vpsrld $20, %ymm2, %ymm3
vpslld $12, %ymm2, %ymm2
vpxor %ymm2, %ymm3, %ymm3
vpsrld $20, %ymm0, %ymm2
vpslld $12, %ymm0, %ymm0
vmovdqu %ymm3, 2976(%esp)
vpxor %ymm0, %ymm2, %ymm0
vpaddd 2656(%esp), %ymm5, %ymm2
vpaddd 2688(%esp), %ymm1, %ymm5
vmovdqu %ymm2, 3008(%esp)
vmovdqu %ymm5, 3040(%esp)
vpxor %ymm2, %ymm4, %ymm2
vpxor %ymm5, %ymm6, %ymm6
vpaddd 2720(%esp), %ymm3, %ymm5
vmovdqu 2208(%esp), %ymm4
vpxor %ymm5, %ymm7, %ymm7
vmovdqu %ymm5, 3136(%esp)
vpshufb %ymm4, %ymm2, %ymm2
vpshufb %ymm4, %ymm6, %ymm6
vpshufb %ymm4, %ymm7, %ymm5
vmovdqu %ymm2, 3072(%esp)
vmovdqu %ymm6, 3104(%esp)
vmovdqu %ymm5, 3200(%esp)
vpaddd 2752(%esp), %ymm0, %ymm2
vpaddd 2848(%esp), %ymm6, %ymm6
vpaddd 2912(%esp), %ymm5, %ymm5
vmovdqu %ymm2, 3168(%esp)
vmovdqu %ymm6, 3264(%esp)
vpxor 2784(%esp), %ymm2, %ymm2
vpxor %ymm6, %ymm1, %ymm6
vpshufb %ymm4, %ymm2, %ymm2
vmovdqu 3072(%esp), %ymm4
vpaddd 2816(%esp), %ymm4, %ymm7
vpxor 2880(%esp), %ymm7, %ymm3
vmovdqu %ymm7, 3232(%esp)
vpsrld $25, %ymm3, %ymm1
vpslld $7, %ymm3, %ymm4
vpxor %ymm4, %ymm1, %ymm7
vpsrld $25, %ymm6, %ymm1
vpslld $7, %ymm6, %ymm6
vpaddd 2944(%esp), %ymm2, %ymm4
vmovdqu %ymm7, 3296(%esp)
vpxor %ymm6, %ymm1, %ymm3
vpxor 2976(%esp), %ymm5, %ymm1
vpxor %ymm4, %ymm0, %ymm0
vmovdqu %ymm4, 3360(%esp)
vmovdqu %ymm3, 3328(%esp)
vpsrld $25, %ymm1, %ymm6
vpslld $7, %ymm1, %ymm1
vpsrld $25, %ymm0, %ymm4
vpslld $7, %ymm0, %ymm0
vpxor %ymm1, %ymm6, %ymm1
vpxor %ymm0, %ymm4, %ymm6
vpaddd 3008(%esp), %ymm3, %ymm0
vpaddd 3040(%esp), %ymm1, %ymm3
vmovdqu %ymm6, 3392(%esp)
vmovdqu %ymm0, 3424(%esp)
vmovdqu %ymm3, 3456(%esp)
vpxor %ymm0, %ymm2, %ymm4
vpxor 3072(%esp), %ymm3, %ymm3
vmovdqu 2592(%esp), %ymm2
vpshufb %ymm2, %ymm4, %ymm0
vpshufb %ymm2, %ymm3, %ymm3
vpaddd 3136(%esp), %ymm6, %ymm4
vpaddd 3168(%esp), %ymm7, %ymm6
vpaddd %ymm0, %ymm5, %ymm5
vpxor 3104(%esp), %ymm4, %ymm7
vmovdqu %ymm6, 3520(%esp)
vmovdqu %ymm5, 3584(%esp)
vmovdqu %ymm4, 3488(%esp)
vpxor 3200(%esp), %ymm6, %ymm6
vpxor 3328(%esp), %ymm5, %ymm5
vpshufb %ymm2, %ymm7, %ymm7
vpshufb %ymm2, %ymm6, %ymm4
vpaddd 3360(%esp), %ymm3, %ymm2
vpsrld $20, %ymm5, %ymm6
vmovdqu %ymm4, 3552(%esp)
vpxor %ymm2, %ymm1, %ymm1
vmovdqu %ymm2, 3616(%esp)
vpslld $12, %ymm5, %ymm2
vpxor %ymm2, %ymm6, %ymm5
vpsrld $20, %ymm1, %ymm6
vpslld $12, %ymm1, %ymm1
vpaddd 3232(%esp), %ymm7, %ymm2
vmovdqu %ymm5, 3648(%esp)
vpxor %ymm1, %ymm6, %ymm1
vpaddd 3264(%esp), %ymm4, %ymm6
vpxor 3392(%esp), %ymm2, %ymm4
vpaddd 3424(%esp), %ymm5, %ymm5
vmovdqu %ymm2, 3680(%esp)
vmovdqu %ymm6, 3712(%esp)
vpxor 3296(%esp), %ymm6, %ymm2
vpsrld $20, %ymm4, %ymm6
vpslld $12, %ymm4, %ymm4
vmovdqu %ymm5, 2496(%esp)
vpxor %ymm5, %ymm0, %ymm5
vpxor %ymm4, %ymm6, %ymm6
vpsrld $20, %ymm2, %ymm4
vpslld $12, %ymm2, %ymm2
vmovdqu 2208(%esp), %ymm0
vmovdqu %ymm6, 3744(%esp)
vpxor %ymm2, %ymm4, %ymm2
vpaddd 3456(%esp), %ymm1, %ymm4
vpaddd 3488(%esp), %ymm6, %ymm6
vpshufb %ymm0, %ymm5, %ymm5
vpxor %ymm4, %ymm3, %ymm3
vpxor %ymm6, %ymm7, %ymm7
vmovdqu %ymm4, 2528(%esp)
vmovdqu %ymm6, 2560(%esp)
vmovdqu %ymm5, 2240(%esp)
vpaddd 3520(%esp), %ymm2, %ymm4
vpshufb %ymm0, %ymm3, %ymm3
vpshufb %ymm0, %ymm7, %ymm6
vpxor 3552(%esp), %ymm4, %ymm7
vmovdqu %ymm3, 2304(%esp)
vmovdqu %ymm4, 2464(%esp)
vpaddd 3584(%esp), %ymm5, %ymm4
vpaddd 3616(%esp), %ymm3, %ymm3
vpshufb %ymm0, %ymm7, %ymm0
vpxor 3648(%esp), %ymm4, %ymm5
vpxor %ymm3, %ymm1, %ymm1
vmovdqu %ymm3, 2336(%esp)
vmovdqu %ymm0, 2272(%esp)
vmovdqu %ymm4, 2368(%esp)
vpsrld $25, %ymm5, %ymm7
vpslld $7, %ymm5, %ymm3
vpsrld $25, %ymm1, %ymm5
vpslld $7, %ymm1, %ymm1
vpaddd 3712(%esp), %ymm0, %ymm0
vpxor %ymm3, %ymm7, %ymm4
vpxor %ymm1, %ymm5, %ymm1
vpxor %ymm0, %ymm2, %ymm7
vmovdqu %ymm4, 2432(%esp)
vmovdqu %ymm1, 2400(%esp)
vpaddd 3680(%esp), %ymm6, %ymm1
vpsrld $25, %ymm7, %ymm4
vpslld $7, %ymm7, %ymm5
vpxor 3744(%esp), %ymm1, %ymm3
vpxor %ymm5, %ymm4, %ymm5
vpsrld $25, %ymm3, %ymm2
vpslld $7, %ymm3, %ymm3
vpxor %ymm3, %ymm2, %ymm2
addl $-2, %esi
jne chacha_blocks_avx2_6
chacha_blocks_avx2_7:
vmovdqu 2496(%esp), %ymm3
vmovdqu 2528(%esp), %ymm7
vmovdqu %ymm6, 1696(%esp)
vmovdqu 2560(%esp), %ymm6
vpaddd 1440(%esp), %ymm3, %ymm4
vpaddd 1472(%esp), %ymm7, %ymm3
vpaddd 2016(%esp), %ymm2, %ymm2
vpaddd 1504(%esp), %ymm6, %ymm6
vmovdqu 2464(%esp), %ymm7
vmovdqu %ymm2, 1728(%esp)
vpaddd 1536(%esp), %ymm7, %ymm7
vmovdqu %ymm7, 1792(%esp)
vpaddd 1568(%esp), %ymm5, %ymm7
vmovdqu 2432(%esp), %ymm5
vpaddd 1600(%esp), %ymm5, %ymm5
vmovdqu %ymm5, 1760(%esp)
vmovdqu 2400(%esp), %ymm5
vpaddd 2048(%esp), %ymm5, %ymm5
testl %edx, %edx
je chacha_blocks_avx2_40
chacha_blocks_avx2_8:
vmovdqu %ymm0, 608(%esp)
vmovdqu 1792(%esp), %ymm0
vmovdqu %ymm1, 576(%esp)
vpunpckldq %ymm3, %ymm4, %ymm1
vpunpckhdq %ymm3, %ymm4, %ymm3
vpunpckldq %ymm0, %ymm6, %ymm2
vpunpckhdq %ymm0, %ymm6, %ymm6
vmovdqu 1760(%esp), %ymm0
vmovdqu 1728(%esp), %ymm4
vmovdqu %ymm3, 640(%esp)
vmovdqu %ymm6, 672(%esp)
vpunpckldq %ymm0, %ymm7, %ymm6
vpunpckldq %ymm4, %ymm5, %ymm3
vpunpckhdq %ymm0, %ymm7, %ymm7
vpunpckhdq %ymm4, %ymm5, %ymm0
vpunpcklqdq %ymm2, %ymm1, %ymm5
vpunpckhqdq %ymm2, %ymm1, %ymm2
vmovdqu 640(%esp), %ymm4
vmovdqu %ymm5, 704(%esp)
vmovdqu %ymm2, 768(%esp)
vmovdqu 672(%esp), %ymm2
vpunpcklqdq %ymm3, %ymm6, %ymm5
vpunpckhqdq %ymm3, %ymm6, %ymm3
vpunpcklqdq %ymm2, %ymm4, %ymm6
vpunpckhqdq %ymm2, %ymm4, %ymm1
vmovdqu %ymm5, 736(%esp)
vmovdqu 2336(%esp), %ymm4
vmovdqu 1696(%esp), %ymm2
vmovdqu %ymm3, 800(%esp)
vmovdqu 608(%esp), %ymm3
vmovdqu %ymm6, 832(%esp)
vmovdqu %ymm1, 896(%esp)
vpunpcklqdq %ymm0, %ymm7, %ymm5
vpunpckhqdq %ymm0, %ymm7, %ymm7
vmovdqu 576(%esp), %ymm0
vpaddd 1952(%esp), %ymm3, %ymm6
vmovdqu %ymm5, 864(%esp)
vmovdqu 2368(%esp), %ymm5
vmovdqu %ymm7, 928(%esp)
vmovdqu 2272(%esp), %ymm3
vpaddd 1984(%esp), %ymm0, %ymm1
vpaddd 1920(%esp), %ymm5, %ymm7
vpaddd 1888(%esp), %ymm4, %ymm5
vpaddd 1632(%esp), %ymm2, %ymm4
vpaddd 1856(%esp), %ymm3, %ymm3
vmovdqu 2240(%esp), %ymm2
vmovdqu 2304(%esp), %ymm0
vpaddd 1824(%esp), %ymm2, %ymm2
vpaddd 1664(%esp), %ymm0, %ymm0
vmovdqu %ymm2, 960(%esp)
vpunpckldq %ymm6, %ymm1, %ymm2
vpunpckhdq %ymm6, %ymm1, %ymm6
vpunpckhdq %ymm5, %ymm7, %ymm1
vmovdqu %ymm2, 992(%esp)
vpunpckldq %ymm5, %ymm7, %ymm2
vpunpckldq %ymm4, %ymm0, %ymm7
vpunpckhdq %ymm4, %ymm0, %ymm4
vmovdqu %ymm1, 1024(%esp)
vmovdqu 960(%esp), %ymm1
vpunpckldq %ymm1, %ymm3, %ymm5
vpunpckhdq %ymm1, %ymm3, %ymm0
vmovdqu 992(%esp), %ymm3
vpunpcklqdq %ymm2, %ymm3, %ymm1
vpunpckhqdq %ymm2, %ymm3, %ymm3
vmovdqu 1024(%esp), %ymm2
vmovdqu %ymm1, 1056(%esp)
vmovdqu %ymm3, 1120(%esp)
vpunpcklqdq %ymm5, %ymm7, %ymm1
vpunpckhqdq %ymm5, %ymm7, %ymm5
vpunpcklqdq %ymm2, %ymm6, %ymm7
vpunpckhqdq %ymm2, %ymm6, %ymm2
vmovdqu 704(%esp), %ymm6
vmovdqu %ymm1, 1088(%esp)
vmovdqu %ymm5, 1152(%esp)
vmovdqu %ymm7, 1184(%esp)
vpunpcklqdq %ymm0, %ymm4, %ymm7
vpunpckhqdq %ymm0, %ymm4, %ymm4
vmovdqu %ymm7, 1216(%esp)
vmovdqu %ymm4, 1248(%esp)
vperm2i128 $32, 736(%esp), %ymm6, %ymm6
vperm2i128 $2, 1056(%esp), %ymm1, %ymm1
vperm2i128 $32, %ymm5, %ymm3, %ymm3
vpxor (%edx), %ymm6, %ymm0
vpxor 32(%edx), %ymm1, %ymm6
vpxor 96(%edx), %ymm3, %ymm5
vmovdqu 768(%esp), %ymm1
vmovdqu 832(%esp), %ymm3
vmovdqu %ymm6, 1280(%esp)
vperm2i128 $2, 1184(%esp), %ymm7, %ymm7
vperm2i128 $32, 800(%esp), %ymm1, %ymm6
vperm2i128 $32, 864(%esp), %ymm3, %ymm1
vpxor 160(%edx), %ymm7, %ymm7
vpxor 128(%edx), %ymm1, %ymm3
vpxor 64(%edx), %ymm6, %ymm6
vmovdqu 928(%esp), %ymm1
vmovdqu %ymm7, 1312(%esp)
vperm2i128 $2, 896(%esp), %ymm1, %ymm7
vperm2i128 $32, %ymm4, %ymm2, %ymm4
vpxor 192(%edx), %ymm7, %ymm7
vpxor 224(%edx), %ymm4, %ymm4
vmovdqu %ymm0, (%eax)
vmovdqu 1280(%esp), %ymm0
vmovdqu %ymm5, 96(%eax)
vmovdqu 1312(%esp), %ymm5
vmovdqu %ymm3, 128(%eax)
vmovdqu %ymm7, 192(%eax)
vmovdqu %ymm0, 32(%eax)
vmovdqu 704(%esp), %ymm3
vmovdqu 1056(%esp), %ymm7
vmovdqu 768(%esp), %ymm0
vmovdqu %ymm6, 64(%eax)
vmovdqu %ymm5, 160(%eax)
vmovdqu %ymm4, 224(%eax)
vperm2i128 $49, 736(%esp), %ymm3, %ymm6
vperm2i128 $49, 1088(%esp), %ymm7, %ymm4
vperm2i128 $49, 800(%esp), %ymm0, %ymm3
vpxor 256(%edx), %ymm6, %ymm5
vpxor 288(%edx), %ymm4, %ymm7
vpxor 320(%edx), %ymm3, %ymm4
vmovdqu 1120(%esp), %ymm6
vmovdqu 832(%esp), %ymm3
vperm2i128 $49, 1152(%esp), %ymm6, %ymm0
vperm2i128 $49, 864(%esp), %ymm3, %ymm6
vpxor 384(%edx), %ymm6, %ymm3
vpxor 352(%edx), %ymm0, %ymm0
vmovdqu 1184(%esp), %ymm6
vmovdqu %ymm3, 1344(%esp)
vperm2i128 $19, 896(%esp), %ymm1, %ymm1
vperm2i128 $49, 1216(%esp), %ymm6, %ymm3
vperm2i128 $49, 1248(%esp), %ymm2, %ymm2
vpxor 448(%edx), %ymm1, %ymm6
vpxor 416(%edx), %ymm3, %ymm3
vpxor 480(%edx), %ymm2, %ymm1
vmovdqu %ymm0, 352(%eax)
vmovdqu 1344(%esp), %ymm0
vmovdqu %ymm5, 256(%eax)
vmovdqu %ymm7, 288(%eax)
vmovdqu %ymm4, 320(%eax)
vmovdqu %ymm3, 416(%eax)
vmovdqu %ymm0, 384(%eax)
vmovdqu %ymm6, 448(%eax)
vmovdqu %ymm1, 480(%eax)
addl $512, %edx
chacha_blocks_avx2_9:
movl 2152(%esp), %esi
addl $512, %eax
addl $-512, %esi
movl %esi, 2152(%esp)
cmpl $512, %esi
jae chacha_blocks_avx2_5
chacha_blocks_avx2_10:
movl %edx, 2156(%esp)
movl %esi, %edx
chacha_blocks_avx2_11:
cmpl $256, %edx
jb chacha_blocks_avx2_17
chacha_blocks_avx2_12:
movl 560(%esp), %ecx
movl %ecx, %esi
addl $1, %esi
movl 564(%esp), %ebx
movl %ebx, %edi
movl %esi, 1380(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $2, %esi
movl %edi, 1412(%esp)
movl %ebx, %edi
movl %esi, 1384(%esp)
movl %ecx, %esi
adcl $0, %edi
addl $3, %esi
movl %edi, 1416(%esp)
movl %ebx, %edi
movl %ecx, 1376(%esp)
adcl $0, %edi
addl $4, %ecx
movl %ebx, 1408(%esp)
adcl $0, %ebx
movl %ecx, 560(%esp)
movl %ebx, 564(%esp)
vpbroadcastd 552(%esp), %xmm7
vmovdqu %xmm7, 240(%esp)
vmovdqu %xmm7, 320(%esp)
vpbroadcastd 556(%esp), %xmm7
movl %esi, 1388(%esp)
vmovdqu %xmm7, 256(%esp)
vmovdqu %xmm7, 304(%esp)
vmovdqu 1376(%esp), %xmm6
vpbroadcastd 2096(%esp), %xmm3
vpbroadcastd 524(%esp), %xmm5
vpbroadcastd 532(%esp), %xmm2
vpbroadcastd 536(%esp), %xmm1
vpbroadcastd 568(%esp), %xmm7
movl %edi, 1420(%esp)
vmovdqu %xmm6, 48(%esp)
vmovdqu %xmm6, 400(%esp)
vmovdqu %xmm3, 80(%esp)
vmovdqu %xmm3, 352(%esp)
vmovdqu %xmm5, 128(%esp)
vmovdqu %xmm5, 368(%esp)
vmovdqu %xmm2, 160(%esp)
vmovdqu %xmm2, 432(%esp)
vmovdqu %xmm1, 176(%esp)
vmovdqu %xmm1, 384(%esp)
vmovdqu %xmm7, 272(%esp)
vmovdqu %xmm7, 416(%esp)
vmovdqu 1408(%esp), %xmm6
vpbroadcastd 516(%esp), %xmm3
vpbroadcastd 520(%esp), %xmm4
vpbroadcastd 2112(%esp), %xmm5
vpbroadcastd 540(%esp), %xmm2
vpbroadcastd 2128(%esp), %xmm1
vpbroadcastd 548(%esp), %xmm0
vpbroadcastd 572(%esp), %xmm7
movl 2148(%esp), %ecx
vmovdqu %xmm6, 64(%esp)
vmovdqu %xmm3, 96(%esp)
vmovdqu %xmm4, 112(%esp)
vmovdqu %xmm5, 144(%esp)
vmovdqu %xmm2, 192(%esp)
vmovdqu %xmm1, 208(%esp)
vmovdqu %xmm0, 224(%esp)
vmovdqu %xmm7, 288(%esp)
vmovdqu %xmm7, 336(%esp)
vmovdqu %xmm4, 16(%esp)
vmovdqu %xmm3, (%esp)
chacha_blocks_avx2_13:
vpaddd 352(%esp), %xmm5, %xmm3
vmovdqu 432(%esp), %xmm7
vpxor 400(%esp), %xmm3, %xmm4
vmovdqu %xmm3, 32(%esp)
vpaddd (%esp), %xmm7, %xmm7
vmovdqu 2160(%esp), %xmm3
vpxor %xmm7, %xmm6, %xmm6
vpshufb %xmm3, %xmm4, %xmm4
vpshufb %xmm3, %xmm6, %xmm6
vmovdqu %xmm7, 464(%esp)
vpaddd %xmm4, %xmm1, %xmm1
vmovdqu 384(%esp), %xmm7
vpaddd %xmm6, %xmm0, %xmm0
vpaddd 16(%esp), %xmm7, %xmm7
vpxor %xmm1, %xmm5, %xmm5
vmovdqu %xmm2, 448(%esp)
vpaddd 368(%esp), %xmm2, %xmm2
vmovdqu %xmm7, 480(%esp)
vpxor 416(%esp), %xmm7, %xmm7
vmovdqu %xmm2, 496(%esp)
vpxor 336(%esp), %xmm2, %xmm2
vpshufb %xmm3, %xmm7, %xmm7
vpshufb %xmm3, %xmm2, %xmm2
vmovdqu %xmm0, 608(%esp)
vpslld $12, %xmm5, %xmm3
vmovdqu %xmm1, 592(%esp)
vpsrld $20, %xmm5, %xmm1
vpxor 432(%esp), %xmm0, %xmm0
vpxor %xmm3, %xmm1, %xmm5
vpsrld $20, %xmm0, %xmm1
vpslld $12, %xmm0, %xmm0
vpxor %xmm0, %xmm1, %xmm1
vpaddd 320(%esp), %xmm7, %xmm0
vpaddd 304(%esp), %xmm2, %xmm3
vmovdqu %xmm2, 576(%esp)
vpxor 384(%esp), %xmm0, %xmm2
vmovdqu %xmm0, 640(%esp)
vmovdqu %xmm3, 656(%esp)
vpxor 448(%esp), %xmm3, %xmm0
vpsrld $20, %xmm2, %xmm3
vpslld $12, %xmm2, %xmm2
vpxor %xmm2, %xmm3, %xmm3
vpsrld $20, %xmm0, %xmm2
vpslld $12, %xmm0, %xmm0
vpxor %xmm0, %xmm2, %xmm0
vpaddd 32(%esp), %xmm5, %xmm2
vmovdqu %xmm2, 688(%esp)
vpxor %xmm2, %xmm4, %xmm2
vmovdqu 2176(%esp), %xmm4
vpshufb %xmm4, %xmm2, %xmm2
vmovdqu %xmm5, 624(%esp)
vpaddd 464(%esp), %xmm1, %xmm5
vmovdqu %xmm2, 720(%esp)
vpxor %xmm5, %xmm6, %xmm6
vmovdqu %xmm5, 704(%esp)
vpaddd 496(%esp), %xmm0, %xmm2
vpaddd 480(%esp), %xmm3, %xmm5
vpshufb %xmm4, %xmm6, %xmm6
vmovdqu %xmm2, 768(%esp)
vpxor %xmm5, %xmm7, %xmm7
vpxor 576(%esp), %xmm2, %xmm2
vmovdqu %xmm5, 752(%esp)
vpshufb %xmm4, %xmm7, %xmm5
vpshufb %xmm4, %xmm2, %xmm2
vmovdqu 720(%esp), %xmm4
vpaddd 592(%esp), %xmm4, %xmm7
vmovdqu %xmm3, 672(%esp)
vmovdqu %xmm6, 736(%esp)
vpaddd 608(%esp), %xmm6, %xmm6
vpxor 624(%esp), %xmm7, %xmm3
vmovdqu %xmm6, 816(%esp)
vpxor %xmm6, %xmm1, %xmm6
vpsrld $25, %xmm3, %xmm1
vpslld $7, %xmm3, %xmm4
vmovdqu %xmm5, 784(%esp)
vmovdqu %xmm7, 800(%esp)
vpxor %xmm4, %xmm1, %xmm7
vpaddd 640(%esp), %xmm5, %xmm5
vpsrld $25, %xmm6, %xmm1
vpslld $7, %xmm6, %xmm6
vpaddd 656(%esp), %xmm2, %xmm4
vpxor %xmm6, %xmm1, %xmm3
vpxor 672(%esp), %xmm5, %xmm1
vpxor %xmm4, %xmm0, %xmm0
vpsrld $25, %xmm1, %xmm6
vpslld $7, %xmm1, %xmm1
vmovdqu %xmm4, 864(%esp)
vpsrld $25, %xmm0, %xmm4
vpslld $7, %xmm0, %xmm0
vpxor %xmm1, %xmm6, %xmm1
vpxor %xmm0, %xmm4, %xmm6
vpaddd 688(%esp), %xmm3, %xmm0
vmovdqu %xmm3, 848(%esp)
vpxor %xmm0, %xmm2, %xmm4
vpaddd 704(%esp), %xmm1, %xmm3
vmovdqu 2160(%esp), %xmm2
vmovdqu %xmm3, 912(%esp)
vmovdqu %xmm0, 896(%esp)
vpshufb %xmm2, %xmm4, %xmm0
vpxor 720(%esp), %xmm3, %xmm3
vpaddd %xmm0, %xmm5, %xmm5
vpshufb %xmm2, %xmm3, %xmm3
vpaddd 752(%esp), %xmm6, %xmm4
vmovdqu %xmm6, 880(%esp)
vpaddd 768(%esp), %xmm7, %xmm6
vmovdqu %xmm7, 832(%esp)
vpxor 736(%esp), %xmm4, %xmm7
vmovdqu %xmm6, 944(%esp)
vpxor 784(%esp), %xmm6, %xmm6
vpshufb %xmm2, %xmm7, %xmm7
vmovdqu %xmm4, 928(%esp)
vpshufb %xmm2, %xmm6, %xmm4
vmovdqu %xmm5, 976(%esp)
vpaddd 864(%esp), %xmm3, %xmm2
vpxor 848(%esp), %xmm5, %xmm5
vpxor %xmm2, %xmm1, %xmm1
vmovdqu %xmm2, 992(%esp)
vpsrld $20, %xmm5, %xmm6
vpslld $12, %xmm5, %xmm2
vpxor %xmm2, %xmm6, %xmm5
vpsrld $20, %xmm1, %xmm6
vpslld $12, %xmm1, %xmm1
vpaddd 800(%esp), %xmm7, %xmm2
vpxor %xmm1, %xmm6, %xmm1
vpaddd 816(%esp), %xmm4, %xmm6
vmovdqu %xmm4, 960(%esp)
vpxor 880(%esp), %xmm2, %xmm4
vmovdqu %xmm2, 1024(%esp)
vmovdqu %xmm6, 1040(%esp)
vpxor 832(%esp), %xmm6, %xmm2
vpsrld $20, %xmm4, %xmm6
vpslld $12, %xmm4, %xmm4
vpxor %xmm4, %xmm6, %xmm6
vpsrld $20, %xmm2, %xmm4
vpslld $12, %xmm2, %xmm2
vmovdqu %xmm5, 1008(%esp)
vpxor %xmm2, %xmm4, %xmm2
vpaddd 896(%esp), %xmm5, %xmm5
vpaddd 912(%esp), %xmm1, %xmm4
vmovdqu %xmm5, 352(%esp)
vpxor %xmm5, %xmm0, %xmm5
vmovdqu 2176(%esp), %xmm0
vpxor %xmm4, %xmm3, %xmm3
vpshufb %xmm0, %xmm5, %xmm5
vpshufb %xmm0, %xmm3, %xmm3
vmovdqu %xmm6, 1056(%esp)
vpaddd 928(%esp), %xmm6, %xmm6
vmovdqu %xmm4, (%esp)
vpxor %xmm6, %xmm7, %xmm7
vpaddd 944(%esp), %xmm2, %xmm4
vmovdqu %xmm6, 16(%esp)
vpshufb %xmm0, %xmm7, %xmm6
vpxor 960(%esp), %xmm4, %xmm7
vmovdqu %xmm3, 400(%esp)
vmovdqu %xmm4, 368(%esp)
vpshufb %xmm0, %xmm7, %xmm0
vpaddd 976(%esp), %xmm5, %xmm4
vpaddd 992(%esp), %xmm3, %xmm3
vmovdqu %xmm5, 336(%esp)
vpxor %xmm3, %xmm1, %xmm1
vpxor 1008(%esp), %xmm4, %xmm5
vmovdqu %xmm3, 304(%esp)
vpsrld $25, %xmm5, %xmm7
vpslld $7, %xmm5, %xmm3
vpsrld $25, %xmm1, %xmm5
vpslld $7, %xmm1, %xmm1
vpxor %xmm1, %xmm5, %xmm1
vmovdqu %xmm0, 416(%esp)
vmovdqu %xmm1, 384(%esp)
vpaddd 1024(%esp), %xmm6, %xmm1
vpaddd 1040(%esp), %xmm0, %xmm0
vmovdqu %xmm4, 320(%esp)
vpxor %xmm3, %xmm7, %xmm4
vpxor 1056(%esp), %xmm1, %xmm3
vpxor %xmm0, %xmm2, %xmm7
vmovdqu %xmm4, 432(%esp)
vpsrld $25, %xmm3, %xmm2
vpslld $7, %xmm3, %xmm3
vpsrld $25, %xmm7, %xmm4
vpslld $7, %xmm7, %xmm5
vpxor %xmm3, %xmm2, %xmm2
vpxor %xmm5, %xmm4, %xmm5
addl $-2, %ecx
jne chacha_blocks_avx2_13
chacha_blocks_avx2_14:
vmovdqu 16(%esp), %xmm4
vmovdqu (%esp), %xmm3
cmpl $0, 2156(%esp)
je chacha_blocks_avx2_39
chacha_blocks_avx2_15:
vmovdqu %xmm6, 32(%esp)
vmovdqu 352(%esp), %xmm7
vmovdqu 368(%esp), %xmm6
vmovdqu %xmm0, 16(%esp)
vpaddd 80(%esp), %xmm7, %xmm0
vpaddd 96(%esp), %xmm3, %xmm3
vpaddd 112(%esp), %xmm4, %xmm4
vpaddd 128(%esp), %xmm6, %xmm7
movl 2156(%esp), %ecx
vpunpckldq %xmm3, %xmm0, %xmm6
vpunpckhdq %xmm3, %xmm0, %xmm3
vpunpckldq %xmm7, %xmm4, %xmm0
vpunpckhdq %xmm7, %xmm4, %xmm4
vpunpcklqdq %xmm0, %xmm6, %xmm7
vpunpckhqdq %xmm0, %xmm6, %xmm0
vpxor 64(%ecx), %xmm0, %xmm6
vpunpcklqdq %xmm4, %xmm3, %xmm0
vpunpckhqdq %xmm4, %xmm3, %xmm3
vpxor (%ecx), %xmm7, %xmm7
vpxor 128(%ecx), %xmm0, %xmm0
vpxor 192(%ecx), %xmm3, %xmm4
vmovdqu %xmm7, (%eax)
vmovdqu %xmm6, 64(%eax)
vmovdqu %xmm4, 192(%eax)
vmovdqu %xmm0, 128(%eax)
vpaddd 144(%esp), %xmm5, %xmm7
vmovdqu 432(%esp), %xmm5
vpaddd 160(%esp), %xmm5, %xmm3
vmovdqu 384(%esp), %xmm5
vpaddd 176(%esp), %xmm5, %xmm5
vpaddd 192(%esp), %xmm2, %xmm6
vpunpckldq %xmm3, %xmm7, %xmm4
vpunpckldq %xmm6, %xmm5, %xmm2
vpunpckhdq %xmm3, %xmm7, %xmm3
vpunpckhdq %xmm6, %xmm5, %xmm6
vpunpcklqdq %xmm2, %xmm4, %xmm7
vpunpckhqdq %xmm2, %xmm4, %xmm2
vpxor 80(%ecx), %xmm2, %xmm4
vpunpcklqdq %xmm6, %xmm3, %xmm2
vpxor 16(%ecx), %xmm7, %xmm0
vpunpckhqdq %xmm6, %xmm3, %xmm5
vpxor 144(%ecx), %xmm2, %xmm7
vpxor 208(%ecx), %xmm5, %xmm3
vmovdqu %xmm7, 144(%eax)
vmovdqu %xmm0, 16(%eax)
vmovdqu %xmm4, 80(%eax)
vmovdqu %xmm3, 208(%eax)
vpaddd 208(%esp), %xmm1, %xmm7
vmovdqu 16(%esp), %xmm1
vmovdqu 320(%esp), %xmm2
vmovdqu 304(%esp), %xmm5
vpaddd 224(%esp), %xmm1, %xmm1
vpaddd 240(%esp), %xmm2, %xmm0
vpaddd 256(%esp), %xmm5, %xmm4
vpunpckldq %xmm1, %xmm7, %xmm3
vpunpckhdq %xmm1, %xmm7, %xmm1
vpunpckldq %xmm4, %xmm0, %xmm7
vpunpckhdq %xmm4, %xmm0, %xmm2
vpunpcklqdq %xmm7, %xmm3, %xmm5
vpunpckhqdq %xmm2, %xmm1, %xmm6
vpunpckhqdq %xmm7, %xmm3, %xmm0
vpunpcklqdq %xmm2, %xmm1, %xmm3
vpxor 32(%ecx), %xmm5, %xmm5
vpxor 224(%ecx), %xmm6, %xmm2
vpxor 160(%ecx), %xmm3, %xmm7
vpxor 96(%ecx), %xmm0, %xmm4
vmovdqu 32(%esp), %xmm1
vmovdqu 416(%esp), %xmm0
vmovdqu %xmm5, 32(%eax)
vmovdqu %xmm2, 224(%eax)
vmovdqu %xmm4, 96(%eax)
vmovdqu %xmm7, 160(%eax)
vmovdqu 400(%esp), %xmm5
vmovdqu 336(%esp), %xmm3
vpaddd 64(%esp), %xmm1, %xmm2
vpaddd 272(%esp), %xmm0, %xmm1
vpaddd 48(%esp), %xmm5, %xmm6
vpaddd 288(%esp), %xmm3, %xmm0
vpunpckldq %xmm2, %xmm6, %xmm7
vpunpckldq %xmm0, %xmm1, %xmm4
vpunpckhdq %xmm2, %xmm6, %xmm5
vpunpckhdq %xmm0, %xmm1, %xmm1
vpunpcklqdq %xmm4, %xmm7, %xmm3
vpxor 48(%ecx), %xmm3, %xmm2
vpunpckhqdq %xmm4, %xmm7, %xmm0
vpunpcklqdq %xmm1, %xmm5, %xmm3
vpunpckhqdq %xmm1, %xmm5, %xmm5
vpxor 112(%ecx), %xmm0, %xmm4
vpxor 176(%ecx), %xmm3, %xmm6
vpxor 240(%ecx), %xmm5, %xmm7
addl $256, %ecx
vmovdqu %xmm2, 48(%eax)
vmovdqu %xmm4, 112(%eax)
vmovdqu %xmm6, 176(%eax)
vmovdqu %xmm7, 240(%eax)
movl %ecx, 2156(%esp)
chacha_blocks_avx2_16:
addl $-256, %edx
addl $256, %eax
chacha_blocks_avx2_17:
vmovdqu 560(%esp), %xmm0
movl %edx, %ecx
testl %edx, %edx
jne chacha_blocks_avx2_19
chacha_blocks_avx2_18:
movl 8(%ebp), %eax
vmovdqu %xmm0, 32(%eax)
vzeroupper
addl $3828, %esp
popl %ebx
popl %edi
popl %esi
movl %ebp, %esp
popl %ebp
ret
chacha_blocks_avx2_19:
movl %ecx, 20(%esp)
xorl %edi, %edi
movl %edx, 2152(%esp)
vmovdqu 2128(%esp), %xmm7
vmovdqu 2112(%esp), %xmm1
vmovdqu 2096(%esp), %xmm6
movl 2156(%esp), %esi
jmp chacha_blocks_avx2_20
chacha_blocks_avx2_33:
movl %ebx, 2152(%esp)
addl $64, %eax
chacha_blocks_avx2_20:
incl %edi
movl %edi, %ebx
shll $6, %ebx
negl %ebx
addl 20(%esp), %ebx
lea 64(%ebx), %ecx
cmpl $64, %ecx
jae chacha_blocks_avx2_28
chacha_blocks_avx2_21:
testl %esi, %esi
je chacha_blocks_avx2_27
chacha_blocks_avx2_22:
testl %ecx, %ecx
je chacha_blocks_avx2_26
chacha_blocks_avx2_23:
movl %eax, 16(%esp)
xorl %edx, %edx
chacha_blocks_avx2_24:
movzbl (%edx,%esi), %eax
movb %al, 64(%esp,%edx)
incl %edx
cmpl %ecx, %edx
jb chacha_blocks_avx2_24
chacha_blocks_avx2_25:
movl 16(%esp), %eax
chacha_blocks_avx2_26:
lea 64(%esp), %esi
chacha_blocks_avx2_27:
movl %eax, 2144(%esp)
lea 64(%esp), %eax
chacha_blocks_avx2_28:
vmovdqu %xmm0, (%esp)
vmovdqa %xmm6, %xmm2
movl %esi, 2156(%esp)
xorl %edx, %edx
movl %eax, 16(%esp)
vmovdqa %xmm1, %xmm3
vmovdqu 2160(%esp), %xmm1
vmovdqa %xmm7, %xmm4
movl 2148(%esp), %esi
vmovdqa %xmm0, %xmm5
vmovdqu 2176(%esp), %xmm0
chacha_blocks_avx2_29:
vpaddd %xmm3, %xmm2, %xmm6
incl %edx
vpxor %xmm6, %xmm5, %xmm2
vpshufb %xmm1, %xmm2, %xmm5
vpaddd %xmm5, %xmm4, %xmm2
lea (%edx,%edx), %eax
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
cmpl %esi, %eax
jne chacha_blocks_avx2_29
chacha_blocks_avx2_30:
vmovdqu 2128(%esp), %xmm7
vmovdqu 2112(%esp), %xmm1
vpaddd %xmm7, %xmm4, %xmm4
vmovdqu 2096(%esp), %xmm6
vpaddd %xmm1, %xmm3, %xmm3
vmovdqu (%esp), %xmm0
vpaddd %xmm6, %xmm2, %xmm2
movl 2156(%esp), %esi
vpaddd %xmm0, %xmm5, %xmm5
movl 16(%esp), %eax
testl %esi, %esi
je chacha_blocks_avx2_32
chacha_blocks_avx2_31:
vpxor (%esi), %xmm2, %xmm2
vpxor 16(%esi), %xmm3, %xmm3
vpxor 32(%esi), %xmm4, %xmm4
vpxor 48(%esi), %xmm5, %xmm5
addl $64, %esi
chacha_blocks_avx2_32:
vmovdqu %xmm2, (%eax)
vmovdqu %xmm3, 16(%eax)
vmovdqu %xmm4, 32(%eax)
vmovdqu %xmm5, 48(%eax)
vpaddq 2080(%esp), %xmm0, %xmm0
cmpl $64, %ecx
ja chacha_blocks_avx2_33
chacha_blocks_avx2_34:
movl 2152(%esp), %edx
cmpl $64, %edx
jae chacha_blocks_avx2_18
chacha_blocks_avx2_35:
testl %edx, %edx
jbe chacha_blocks_avx2_18
chacha_blocks_avx2_36:
movl 2144(%esp), %esi
xorl %ebx, %ebx
chacha_blocks_avx2_37:
movzbl (%ebx,%eax), %ecx
movb %cl, (%ebx,%esi)
incl %ebx
cmpl %edx, %ebx
jb chacha_blocks_avx2_37
jmp chacha_blocks_avx2_18
chacha_blocks_avx2_39:
vmovdqu %xmm1, (%esp)
vmovdqu %xmm0, 16(%esp)
vmovdqu 352(%esp), %xmm0
vmovdqu 368(%esp), %xmm1
vmovdqu %xmm6, 32(%esp)
vpaddd 80(%esp), %xmm0, %xmm0
vpaddd 96(%esp), %xmm3, %xmm3
vpaddd 112(%esp), %xmm4, %xmm7
vpaddd 128(%esp), %xmm1, %xmm6
vpunpckldq %xmm3, %xmm0, %xmm4
vpunpckldq %xmm6, %xmm7, %xmm1
vmovdqu %xmm2, 448(%esp)
vpunpcklqdq %xmm1, %xmm4, %xmm2
vpunpckhqdq %xmm1, %xmm4, %xmm4
vpunpckhdq %xmm3, %xmm0, %xmm3
vpunpckhdq %xmm6, %xmm7, %xmm6
vpunpcklqdq %xmm6, %xmm3, %xmm7
vmovdqu %xmm2, (%eax)
vmovdqu %xmm4, 64(%eax)
vmovdqu %xmm7, 128(%eax)
vpunpckhqdq %xmm6, %xmm3, %xmm0
vpaddd 144(%esp), %xmm5, %xmm1
vmovdqu 432(%esp), %xmm5
vmovdqu 384(%esp), %xmm2
vmovdqu 448(%esp), %xmm4
vpaddd 160(%esp), %xmm5, %xmm5
vpaddd 176(%esp), %xmm2, %xmm3
vpaddd 192(%esp), %xmm4, %xmm7
vpunpckldq %xmm5, %xmm1, %xmm6
vpunpckldq %xmm7, %xmm3, %xmm2
vmovdqu %xmm0, 192(%eax)
vpunpcklqdq %xmm2, %xmm6, %xmm0
vpunpckhqdq %xmm2, %xmm6, %xmm2
vpunpckhdq %xmm5, %xmm1, %xmm5
vpunpckhdq %xmm7, %xmm3, %xmm3
vpunpcklqdq %xmm3, %xmm5, %xmm1
vpunpckhqdq %xmm3, %xmm5, %xmm7
vmovdqu %xmm0, 16(%eax)
vmovdqu %xmm2, 80(%eax)
vmovdqu %xmm1, 144(%eax)
vmovdqu %xmm7, 208(%eax)
vmovdqu 16(%esp), %xmm3
vmovdqu (%esp), %xmm0
vmovdqu 320(%esp), %xmm5
vmovdqu 304(%esp), %xmm2
vpaddd 224(%esp), %xmm3, %xmm4
vpaddd 208(%esp), %xmm0, %xmm6
vpaddd 240(%esp), %xmm5, %xmm1
vpaddd 256(%esp), %xmm2, %xmm3
vpunpckldq %xmm4, %xmm6, %xmm7
vpunpckldq %xmm3, %xmm1, %xmm0
vpunpckhdq %xmm4, %xmm6, %xmm4
vpunpckhdq %xmm3, %xmm1, %xmm1
vpunpcklqdq %xmm0, %xmm7, %xmm5
vpunpcklqdq %xmm1, %xmm4, %xmm6
vpunpckhqdq %xmm1, %xmm4, %xmm3
vmovdqu 32(%esp), %xmm1
vmovdqu 416(%esp), %xmm4
vmovdqu %xmm5, 32(%eax)
vmovdqu %xmm6, 160(%eax)
vmovdqu %xmm3, 224(%eax)
vpunpckhqdq %xmm0, %xmm7, %xmm7
vmovdqu 400(%esp), %xmm5
vmovdqu 336(%esp), %xmm0
vpaddd 64(%esp), %xmm1, %xmm2
vpaddd 272(%esp), %xmm4, %xmm1
vpaddd 48(%esp), %xmm5, %xmm6
vpaddd 288(%esp), %xmm0, %xmm4
vmovdqu %xmm7, 96(%eax)
vpunpckldq %xmm2, %xmm6, %xmm7
vpunpckldq %xmm4, %xmm1, %xmm5
vpunpckhdq %xmm2, %xmm6, %xmm2
vpunpckhdq %xmm4, %xmm1, %xmm6
vpunpcklqdq %xmm5, %xmm7, %xmm3
vpunpckhqdq %xmm5, %xmm7, %xmm5
vpunpcklqdq %xmm6, %xmm2, %xmm0
vpunpckhqdq %xmm6, %xmm2, %xmm1
vmovdqu %xmm3, 48(%eax)
vmovdqu %xmm5, 112(%eax)
vmovdqu %xmm0, 176(%eax)
vmovdqu %xmm1, 240(%eax)
jmp chacha_blocks_avx2_16
chacha_blocks_avx2_40:
vmovdqu %ymm1, 576(%esp)
vmovdqu 1792(%esp), %ymm2
vmovdqu %ymm0, 608(%esp)
vpunpckldq %ymm3, %ymm4, %ymm1
vpunpckhdq %ymm3, %ymm4, %ymm3
vpunpckldq %ymm2, %ymm6, %ymm0
vpunpckhdq %ymm2, %ymm6, %ymm6
vmovdqu 1760(%esp), %ymm2
vmovdqu %ymm3, (%esp)
vmovdqu 1728(%esp), %ymm3
vmovdqu %ymm6, 32(%esp)
vpunpckldq %ymm2, %ymm7, %ymm6
vpunpckhdq %ymm2, %ymm7, %ymm2
vpunpckldq %ymm3, %ymm5, %ymm4
vpunpckhdq %ymm3, %ymm5, %ymm7
vpunpcklqdq %ymm0, %ymm1, %ymm3
vpunpckhqdq %ymm0, %ymm1, %ymm0
vpunpcklqdq %ymm4, %ymm6, %ymm5
vpunpckhqdq %ymm4, %ymm6, %ymm6
vperm2i128 $32, %ymm6, %ymm0, %ymm1
vmovdqu %ymm1, 96(%esp)
vperm2i128 $49, %ymm6, %ymm0, %ymm1
vmovdqu 32(%esp), %ymm0
vmovdqu (%esp), %ymm6
vmovdqu %ymm1, 160(%esp)
vpunpcklqdq %ymm0, %ymm6, %ymm1
vperm2i128 $32, %ymm5, %ymm3, %ymm4
vmovdqu %ymm4, 64(%esp)
vpunpcklqdq %ymm7, %ymm2, %ymm4
vperm2i128 $49, %ymm5, %ymm3, %ymm5
vmovdqu %ymm5, 128(%esp)
vpunpckhqdq %ymm0, %ymm6, %ymm5
vpunpckhqdq %ymm7, %ymm2, %ymm0
vmovdqu 608(%esp), %ymm2
vperm2i128 $32, %ymm4, %ymm1, %ymm7
vmovdqu %ymm7, 192(%esp)
vpaddd 1952(%esp), %ymm2, %ymm3
vperm2i128 $32, %ymm0, %ymm5, %ymm6
vperm2i128 $49, %ymm0, %ymm5, %ymm7
vmovdqu 576(%esp), %ymm5
vmovdqu 1696(%esp), %ymm0
vmovdqu %ymm6, 224(%esp)
vmovdqu 2336(%esp), %ymm6
vmovdqu %ymm7, 288(%esp)
vmovdqu 2304(%esp), %ymm7
vpaddd 1888(%esp), %ymm6, %ymm2
vmovdqu 2272(%esp), %ymm6
vpaddd 1664(%esp), %ymm7, %ymm7
vpaddd 1856(%esp), %ymm6, %ymm6
vperm2i128 $49, %ymm4, %ymm1, %ymm1
vmovdqu 2368(%esp), %ymm4
vmovdqu %ymm1, 256(%esp)
vpaddd 1984(%esp), %ymm5, %ymm1
vpaddd 1920(%esp), %ymm4, %ymm5
vpaddd 1632(%esp), %ymm0, %ymm4
vmovdqu 2240(%esp), %ymm0
vpaddd 1824(%esp), %ymm0, %ymm0
vmovdqu %ymm0, 320(%esp)
vpunpckldq %ymm3, %ymm1, %ymm0
vpunpckhdq %ymm3, %ymm1, %ymm1
vpunpckhdq %ymm2, %ymm5, %ymm3
vmovdqu %ymm0, 352(%esp)
vpunpckldq %ymm2, %ymm5, %ymm0
vpunpckldq %ymm4, %ymm7, %ymm2
vpunpckhdq %ymm4, %ymm7, %ymm7
vmovdqu %ymm3, 384(%esp)
vmovdqu 320(%esp), %ymm3
vpunpckldq %ymm3, %ymm6, %ymm5
vpunpckhdq %ymm3, %ymm6, %ymm6
vpunpcklqdq %ymm5, %ymm2, %ymm3
vmovdqu %ymm6, 416(%esp)
vmovdqu 352(%esp), %ymm6
vpunpcklqdq %ymm0, %ymm6, %ymm4
vpunpckhqdq %ymm0, %ymm6, %ymm6
vpunpckhqdq %ymm5, %ymm2, %ymm0
vperm2i128 $32, %ymm0, %ymm6, %ymm5
vperm2i128 $49, %ymm0, %ymm6, %ymm0
vmovdqu %ymm0, 480(%esp)
vmovdqu 416(%esp), %ymm0
vmovdqu %ymm5, 96(%eax)
vmovdqu 192(%esp), %ymm5
vperm2i128 $32, %ymm3, %ymm4, %ymm2
vperm2i128 $49, %ymm3, %ymm4, %ymm3
vmovdqu 384(%esp), %ymm4
vmovdqu %ymm3, 448(%esp)
vmovdqu %ymm2, 32(%eax)
vmovdqu 96(%esp), %ymm2
vmovdqu %ymm5, 128(%eax)
vmovdqu 288(%esp), %ymm5
vpunpcklqdq %ymm4, %ymm1, %ymm6
vpunpcklqdq %ymm0, %ymm7, %ymm3
vpunpckhqdq %ymm4, %ymm1, %ymm4
vpunpckhqdq %ymm0, %ymm7, %ymm1
vmovdqu %ymm2, 64(%eax)
vmovdqu 160(%esp), %ymm2
vmovdqu %ymm5, 448(%eax)
vmovdqu %ymm2, 320(%eax)
vperm2i128 $32, %ymm3, %ymm6, %ymm0
vmovdqu %ymm0, 160(%eax)
vmovdqu 224(%esp), %ymm0
vperm2i128 $49, %ymm3, %ymm6, %ymm6
vmovdqu 64(%esp), %ymm3
vmovdqu %ymm0, 192(%eax)
vmovdqu 448(%esp), %ymm0
vmovdqu %ymm6, 416(%eax)
vmovdqu %ymm3, (%eax)
vmovdqu 480(%esp), %ymm3
vmovdqu %ymm0, 288(%eax)
vmovdqu %ymm3, 352(%eax)
vperm2i128 $32, %ymm1, %ymm4, %ymm7
vmovdqu %ymm7, 224(%eax)
vmovdqu 128(%esp), %ymm7
vperm2i128 $49, %ymm1, %ymm4, %ymm1
vmovdqu 256(%esp), %ymm4
vmovdqu %ymm7, 256(%eax)
vmovdqu %ymm1, 480(%eax)
vmovdqu %ymm4, 384(%eax)
jmp chacha_blocks_avx2_9
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

SECTION_RODATA

.p2align 4,,15
chacha_constants:
.long 0x61707865,0x3320646e,0x79622d32,0x6b206574 /* "expand 32-byte k" */
.byte 2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13       /* pshufb rotate by 16 */
.byte 3,0,1,2,7,4,5,6,11,8,9,10,15,12,13,14       /* pshufb rotate by 8 */



