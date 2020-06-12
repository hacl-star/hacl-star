.code
ALIGN 16
check_aesni proc
  mov r9, rbx
  mov rcx, 0
  mov rax, 1
  cpuid
  mov rax, rcx
  and rax, 33554432
  shr rax, 24
  and rcx, 2
  and rax, rcx
  mov rbx, r9
  ret
check_aesni endp
ALIGN 16
check_sha proc
  mov r9, rbx
  mov rax, 7
  mov rcx, 0
  cpuid
  and rbx, 536870912
  mov rax, rbx
  mov rbx, r9
  ret
check_sha endp
ALIGN 16
check_adx_bmi2 proc
  mov r9, rbx
  mov rax, 7
  mov rcx, 0
  cpuid
  mov rax, rbx
  and rax, 524288
  shr rax, 11
  and rbx, 256
  and rax, rbx
  mov rbx, r9
  ret
check_adx_bmi2 endp
ALIGN 16
check_avx proc
  mov r9, rbx
  mov rcx, 0
  mov rax, 1
  cpuid
  mov rax, rcx
  and rax, 268435456
  shr rax, 27
  mov rbx, r9
  ret
check_avx endp
ALIGN 16
check_avx2 proc
  mov r9, rbx
  mov rax, 7
  mov rcx, 0
  cpuid
  and rbx, 32
  mov rax, rbx
  mov rbx, r9
  ret
check_avx2 endp
ALIGN 16
check_movbe proc
  mov r9, rbx
  mov rcx, 0
  mov rax, 1
  cpuid
  mov rax, rcx
  and rax, 4194304
  shr rax, 21
  mov rbx, r9
  ret
check_movbe endp
ALIGN 16
check_sse proc
  mov r9, rbx
  mov rcx, 0
  mov rax, 1
  cpuid
  mov rax, rcx
  and rax, 524288
  and rcx, 512
  and rdx, 67108864
  shr rax, 10
  shr rdx, 17
  and rax, rdx
  and rax, rcx
  mov rbx, r9
  ret
check_sse endp
ALIGN 16
check_rdrand proc
  mov r9, rbx
  mov rcx, 0
  mov rax, 1
  cpuid
  mov rax, rcx
  and rax, 1073741824
  shr rax, 29
  mov rbx, r9
  ret
check_rdrand endp
end
