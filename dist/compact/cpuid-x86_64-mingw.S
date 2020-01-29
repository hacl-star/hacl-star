.text
.global check_aesni
check_aesni:
  mov %rbx, %r9
  mov $0, %rcx
  mov $1, %rax
  cpuid
  mov %rcx, %rax
  and $33554432, %rax
  shr $24, %rax
  and $2, %rcx
  and %rcx, %rax
  mov %r9, %rbx
  ret

.global check_sha
check_sha:
  mov %rbx, %r9
  mov $7, %rax
  mov $0, %rcx
  cpuid
  and $536870912, %rbx
  mov %rbx, %rax
  mov %r9, %rbx
  ret

.global check_adx_bmi2
check_adx_bmi2:
  mov %rbx, %r9
  mov $7, %rax
  mov $0, %rcx
  cpuid
  mov %rbx, %rax
  and $524288, %rax
  shr $11, %rax
  and $256, %rbx
  and %rbx, %rax
  mov %r9, %rbx
  ret

.global check_avx
check_avx:
  mov %rbx, %r9
  mov $0, %rcx
  mov $1, %rax
  cpuid
  mov %rcx, %rax
  and $268435456, %rax
  shr $27, %rax
  mov %r9, %rbx
  ret

.global check_avx2
check_avx2:
  mov %rbx, %r9
  mov $7, %rax
  mov $0, %rcx
  cpuid
  and $32, %rbx
  mov %rbx, %rax
  mov %r9, %rbx
  ret


