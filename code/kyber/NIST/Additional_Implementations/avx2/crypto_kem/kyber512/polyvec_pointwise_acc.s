.global polyvec_pointwise_acc_k2
polyvec_pointwise_acc_k2:
mov		%rsp,%r11
and		$31,%r11
sub		%r11,%rsp

vmovdqa		_16xqinv(%rip),%ymm0
vmovdqa		_16xq(%rip),%ymm1
vmovdqa		_16xmontsq(%rip),%ymm2

xor		%eax,%eax

_looptop2:
#load a
vmovdqa		(%rsi),%ymm4
vmovdqa		32(%rsi),%ymm5
vmovdqa		64(%rsi),%ymm6
vmovdqa		512(%rsi),%ymm7
vmovdqa		544(%rsi),%ymm8
vmovdqa		576(%rsi),%ymm9

#mul montsq
vpmullw		%ymm2,%ymm4,%ymm3
vpmulhw		%ymm2,%ymm4,%ymm10
vpmullw		%ymm2,%ymm5,%ymm4
vpmulhw		%ymm2,%ymm5,%ymm11
vpmullw		%ymm2,%ymm6,%ymm5
vpmulhw		%ymm2,%ymm6,%ymm12
vpmullw		%ymm2,%ymm7,%ymm6
vpmulhw		%ymm2,%ymm7,%ymm13
vpmullw		%ymm2,%ymm8,%ymm7
vpmulhw		%ymm2,%ymm8,%ymm14
vpmullw		%ymm2,%ymm9,%ymm8
vpmulhw		%ymm2,%ymm9,%ymm15

#reduce
vpmullw		%ymm0,%ymm3,%ymm3
vpmullw		%ymm0,%ymm4,%ymm4
vpmullw		%ymm0,%ymm5,%ymm5
vpmullw		%ymm0,%ymm6,%ymm6
vpmullw		%ymm0,%ymm7,%ymm7
vpmullw		%ymm0,%ymm8,%ymm8
vpmulhw		%ymm1,%ymm3,%ymm3
vpmulhw		%ymm1,%ymm4,%ymm4
vpmulhw		%ymm1,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm7,%ymm7
vpmulhw		%ymm1,%ymm8,%ymm8
vpsubw		%ymm3,%ymm10,%ymm3
vpsubw		%ymm4,%ymm11,%ymm4
vpsubw		%ymm5,%ymm12,%ymm5
vpsubw		%ymm6,%ymm13,%ymm6
vpsubw		%ymm7,%ymm14,%ymm7
vpsubw		%ymm8,%ymm15,%ymm8

#load b
vmovdqa		(%rdx),%ymm9
vmovdqa		32(%rdx),%ymm10
vmovdqa		64(%rdx),%ymm11
vmovdqa		512(%rdx),%ymm12
vmovdqa		544(%rdx),%ymm13
vmovdqa		576(%rdx),%ymm14

#mul
vpmullw		%ymm3,%ymm9,%ymm15
vpmulhw		%ymm3,%ymm9,%ymm9
vpmullw		%ymm4,%ymm10,%ymm3
vpmulhw		%ymm4,%ymm10,%ymm10
vpmullw		%ymm5,%ymm11,%ymm4
vpmulhw		%ymm5,%ymm11,%ymm11
vpmullw		%ymm6,%ymm12,%ymm5
vpmulhw		%ymm6,%ymm12,%ymm12
vpmullw		%ymm7,%ymm13,%ymm6
vpmulhw		%ymm7,%ymm13,%ymm13
vpmullw		%ymm8,%ymm14,%ymm7
vpmulhw		%ymm8,%ymm14,%ymm14

#reduce
vpmullw		%ymm0,%ymm15,%ymm15
vpmullw		%ymm0,%ymm3,%ymm3
vpmullw		%ymm0,%ymm4,%ymm4
vpmullw		%ymm0,%ymm5,%ymm5
vpmullw		%ymm0,%ymm6,%ymm6
vpmullw		%ymm0,%ymm7,%ymm7
vpmulhw		%ymm1,%ymm15,%ymm15
vpmulhw		%ymm1,%ymm3,%ymm3
vpmulhw		%ymm1,%ymm4,%ymm4
vpmulhw		%ymm1,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm7,%ymm7
vpsubw		%ymm15,%ymm9,%ymm15
vpsubw		%ymm3,%ymm10,%ymm3
vpsubw		%ymm4,%ymm11,%ymm4
vpsubw		%ymm5,%ymm12,%ymm5
vpsubw		%ymm6,%ymm13,%ymm6
vpsubw		%ymm7,%ymm14,%ymm7

#add
vpaddw		%ymm15,%ymm5,%ymm5
vpaddw		%ymm3,%ymm6,%ymm6
vpaddw		%ymm4,%ymm7,%ymm7

#reduce 2
vmovdqa		_16xv(%rip),%ymm3
vpmulhw		%ymm3,%ymm5,%ymm8
vpmulhw		%ymm3,%ymm6,%ymm9
vpmulhw		%ymm3,%ymm7,%ymm10
vpsraw		$11,%ymm8,%ymm8
vpsraw		$11,%ymm9,%ymm9
vpsraw		$11,%ymm10,%ymm10
vpmullw		%ymm1,%ymm8,%ymm8
vpmullw		%ymm1,%ymm9,%ymm9
vpmullw		%ymm1,%ymm10,%ymm10
vpsubw		%ymm8,%ymm5,%ymm5
vpsubw		%ymm9,%ymm6,%ymm6
vpsubw		%ymm10,%ymm7,%ymm7

#store
vmovdqa		%ymm5,(%rdi)
vmovdqa		%ymm6,32(%rdi)
vmovdqa		%ymm7,64(%rdi)

add		$1,%eax
add		$96,%rdi
add		$96,%rsi
add		$96,%rdx
cmp		$5,%eax
jb _looptop2

#load
vmovdqa		(%rsi),%ymm4
vmovdqa		512(%rsi),%ymm7
vmovdqa		(%rdx),%ymm9
vmovdqa		512(%rdx),%ymm12

#mul montsq
vpmullw		%ymm2,%ymm4,%ymm3
vpmulhw		%ymm2,%ymm4,%ymm10
vpmullw		%ymm2,%ymm7,%ymm6
vpmulhw		%ymm2,%ymm7,%ymm13

#reduce
vpmullw		%ymm0,%ymm3,%ymm3
vpmullw		%ymm0,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm3,%ymm3
vpmulhw		%ymm1,%ymm6,%ymm6
vpsubw		%ymm3,%ymm10,%ymm3
vpsubw		%ymm6,%ymm13,%ymm6

#mul
vpmullw		%ymm3,%ymm9,%ymm15
vpmulhw		%ymm3,%ymm9,%ymm9
vpmullw		%ymm6,%ymm12,%ymm5
vpmulhw		%ymm6,%ymm12,%ymm12

#reduce
vpmullw		%ymm0,%ymm15,%ymm15
vpmullw		%ymm0,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm15,%ymm15
vpmulhw		%ymm1,%ymm5,%ymm5
vpsubw		%ymm15,%ymm9,%ymm15
vpsubw		%ymm5,%ymm12,%ymm5

#add
vpaddw		%ymm15,%ymm5,%ymm5

#reduce 2
vmovdqa		_16xv(%rip),%ymm3
vpmulhw		%ymm3,%ymm5,%ymm8
vpsraw		$11,%ymm8,%ymm8
vpmullw		%ymm1,%ymm8,%ymm8
vpsubw		%ymm8,%ymm5,%ymm5

#store
vmovdqa		%ymm5,(%rdi)

add		%r11,%rsp
ret

.global polyvec_pointwise_acc_k3
polyvec_pointwise_acc_k3:
mov		%rsp,%r11
and		$31,%r11
sub		%r11,%rsp

vmovdqa		_16xqinv(%rip),%ymm0
vmovdqa		_16xq(%rip),%ymm1
vmovdqa		_16xmontsq(%rip),%ymm2

xor		%eax,%eax

_looptop3:
#load a
vmovdqa		(%rsi),%ymm4
vmovdqa		32(%rsi),%ymm5
vmovdqa		512(%rsi),%ymm6
vmovdqa		544(%rsi),%ymm7
vmovdqa		1024(%rsi),%ymm8
vmovdqa		1056(%rsi),%ymm9

#mul montsq
vpmullw		%ymm2,%ymm4,%ymm3
vpmulhw		%ymm2,%ymm4,%ymm10
vpmullw		%ymm2,%ymm5,%ymm4
vpmulhw		%ymm2,%ymm5,%ymm11
vpmullw		%ymm2,%ymm6,%ymm5
vpmulhw		%ymm2,%ymm6,%ymm12
vpmullw		%ymm2,%ymm7,%ymm6
vpmulhw		%ymm2,%ymm7,%ymm13
vpmullw		%ymm2,%ymm8,%ymm7
vpmulhw		%ymm2,%ymm8,%ymm14
vpmullw		%ymm2,%ymm9,%ymm8
vpmulhw		%ymm2,%ymm9,%ymm15

#reduce
vpmullw		%ymm0,%ymm3,%ymm3
vpmullw		%ymm0,%ymm4,%ymm4
vpmullw		%ymm0,%ymm5,%ymm5
vpmullw		%ymm0,%ymm6,%ymm6
vpmullw		%ymm0,%ymm7,%ymm7
vpmullw		%ymm0,%ymm8,%ymm8
vpmulhw		%ymm1,%ymm3,%ymm3
vpmulhw		%ymm1,%ymm4,%ymm4
vpmulhw		%ymm1,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm7,%ymm7
vpmulhw		%ymm1,%ymm8,%ymm8
vpsubw		%ymm3,%ymm10,%ymm3
vpsubw		%ymm4,%ymm11,%ymm4
vpsubw		%ymm5,%ymm12,%ymm5
vpsubw		%ymm6,%ymm13,%ymm6
vpsubw		%ymm7,%ymm14,%ymm7
vpsubw		%ymm8,%ymm15,%ymm8

#load b
vmovdqa		(%rdx),%ymm9
vmovdqa		32(%rdx),%ymm10
vmovdqa		512(%rdx),%ymm11
vmovdqa		544(%rdx),%ymm12
vmovdqa		1024(%rdx),%ymm13
vmovdqa		1056(%rdx),%ymm14

#mul
vpmullw		%ymm3,%ymm9,%ymm15
vpmulhw		%ymm3,%ymm9,%ymm9
vpmullw		%ymm4,%ymm10,%ymm3
vpmulhw		%ymm4,%ymm10,%ymm10
vpmullw		%ymm5,%ymm11,%ymm4
vpmulhw		%ymm5,%ymm11,%ymm11
vpmullw		%ymm6,%ymm12,%ymm5
vpmulhw		%ymm6,%ymm12,%ymm12
vpmullw		%ymm7,%ymm13,%ymm6
vpmulhw		%ymm7,%ymm13,%ymm13
vpmullw		%ymm8,%ymm14,%ymm7
vpmulhw		%ymm8,%ymm14,%ymm14

#reduce
vpmullw		%ymm0,%ymm15,%ymm15
vpmullw		%ymm0,%ymm3,%ymm3
vpmullw		%ymm0,%ymm4,%ymm4
vpmullw		%ymm0,%ymm5,%ymm5
vpmullw		%ymm0,%ymm6,%ymm6
vpmullw		%ymm0,%ymm7,%ymm7
vpmulhw		%ymm1,%ymm15,%ymm15
vpmulhw		%ymm1,%ymm3,%ymm3
vpmulhw		%ymm1,%ymm4,%ymm4
vpmulhw		%ymm1,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm7,%ymm7
vpsubw		%ymm15,%ymm9,%ymm15
vpsubw		%ymm3,%ymm10,%ymm3
vpsubw		%ymm4,%ymm11,%ymm4
vpsubw		%ymm5,%ymm12,%ymm5
vpsubw		%ymm6,%ymm13,%ymm6
vpsubw		%ymm7,%ymm14,%ymm7

#add
vpaddw		%ymm15,%ymm4,%ymm4
vpaddw		%ymm3,%ymm5,%ymm5
vpaddw		%ymm4,%ymm6,%ymm6
vpaddw		%ymm5,%ymm7,%ymm7

#reduce 2
vmovdqa		_16xv(%rip),%ymm3
vpmulhw		%ymm3,%ymm6,%ymm8
vpmulhw		%ymm3,%ymm7,%ymm9
vpsraw		$11,%ymm8,%ymm8
vpsraw		$11,%ymm9,%ymm9
vpmullw		%ymm1,%ymm8,%ymm8
vpmullw		%ymm1,%ymm9,%ymm9
vpsubw		%ymm8,%ymm6,%ymm6
vpsubw		%ymm9,%ymm7,%ymm7

#store
vmovdqa		%ymm6,(%rdi)
vmovdqa		%ymm7,32(%rdi)

add		$1,%eax
add		$64,%rdi
add		$64,%rsi
add		$64,%rdx
cmp		$8,%eax
jb _looptop3

add		%r11,%rsp
ret

.global polyvec_pointwise_acc_k4
polyvec_pointwise_acc_k4:
mov		%rsp,%r11
and		$31,%r11
sub		%r11,%rsp

vmovdqa		_16xqinv(%rip),%ymm0
vmovdqa		_16xq(%rip),%ymm1
vmovdqa		_16xmontsq(%rip),%ymm2
vmovdqa		_16xv(%rip),%ymm3

xor		%eax,%eax

_looptop4:
#load a
vmovdqa		(%rsi),%ymm6
vmovdqa		512(%rsi),%ymm7
vmovdqa		1024(%rsi),%ymm8
vmovdqa		1536(%rsi),%ymm9

#mul montsq
vpmullw		%ymm2,%ymm6,%ymm5
vpmulhw		%ymm2,%ymm6,%ymm10
vpmullw		%ymm2,%ymm7,%ymm6
vpmulhw		%ymm2,%ymm7,%ymm11
vpmullw		%ymm2,%ymm8,%ymm7
vpmulhw		%ymm2,%ymm8,%ymm12
vpmullw		%ymm2,%ymm9,%ymm8
vpmulhw		%ymm2,%ymm9,%ymm13

#reduce
vpmullw		%ymm0,%ymm5,%ymm5
vpmullw		%ymm0,%ymm6,%ymm6
vpmullw		%ymm0,%ymm7,%ymm7
vpmullw		%ymm0,%ymm8,%ymm8
vpmulhw		%ymm1,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm7,%ymm7
vpmulhw		%ymm1,%ymm8,%ymm8
vpsubw		%ymm5,%ymm10,%ymm5
vpsubw		%ymm6,%ymm11,%ymm6
vpsubw		%ymm7,%ymm12,%ymm7
vpsubw		%ymm8,%ymm13,%ymm8

#load b
vmovdqa		(%rdx),%ymm9
vmovdqa		512(%rdx),%ymm10
vmovdqa		1024(%rdx),%ymm11
vmovdqa		1536(%rdx),%ymm12

#mul
vpmullw		%ymm5,%ymm9,%ymm4
vpmulhw		%ymm5,%ymm9,%ymm9
vpmullw		%ymm6,%ymm10,%ymm5
vpmulhw		%ymm6,%ymm10,%ymm10
vpmullw		%ymm7,%ymm11,%ymm6
vpmulhw		%ymm7,%ymm11,%ymm11
vpmullw		%ymm8,%ymm12,%ymm7
vpmulhw		%ymm8,%ymm12,%ymm12

#reduce
vpmullw		%ymm0,%ymm4,%ymm4
vpmullw		%ymm0,%ymm5,%ymm5
vpmullw		%ymm0,%ymm6,%ymm6
vpmullw		%ymm0,%ymm7,%ymm7
vpmulhw		%ymm1,%ymm4,%ymm4
vpmulhw		%ymm1,%ymm5,%ymm5
vpmulhw		%ymm1,%ymm6,%ymm6
vpmulhw		%ymm1,%ymm7,%ymm7
vpsubw		%ymm4,%ymm9,%ymm4
vpsubw		%ymm5,%ymm10,%ymm5
vpsubw		%ymm6,%ymm11,%ymm6
vpsubw		%ymm7,%ymm12,%ymm7

#add
vpaddw		%ymm4,%ymm5,%ymm5
vpaddw		%ymm5,%ymm6,%ymm6
vpaddw		%ymm6,%ymm7,%ymm7

#reduce 2
vpmulhw		%ymm3,%ymm7,%ymm8
vpsraw		$11,%ymm8,%ymm8
vpmullw		%ymm1,%ymm8,%ymm8
vpsubw		%ymm8,%ymm7,%ymm8

#store
vmovdqa		%ymm8,(%rdi)

add		$1,%eax
add		$32,%rdi
add		$32,%rsi
add		$32,%rdx
cmp		$16,%eax
jb _looptop4

add		%r11,%rsp
ret
