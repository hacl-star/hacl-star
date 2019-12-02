.text
.global _x64_poly1305
_x64_poly1305:
  mov %rdi, %rax
  mov %rsi, %r11
  movq %rcx, 184(%rdi)
  push %rbx
  push %rbp
  push %rax
  push %r11
  push %r12
  push %r13
  push %r14
  push %r15
  movq 24(%rdi), %r11
  movq 32(%rdi), %r12
  mov $1152921487695413247, %rcx
  and %rcx, %r11
  mov $1152921487695413244, %rcx
  and %rcx, %r12
  movq %r11, 24(%rdi)
  movq %r12, 32(%rdi)
  mov %rdx, %rax
  and $15, %rax
  sub %rax, %rdx
  movq %rax, 56(%rdi)
  movq %rdx, 64(%rdi)
  mov $1, %rcx
  shr $4, %rdx
  mov %rdx, %r15
  movq 24(%rdi), %r11
  movq 32(%rdi), %r13
  movq 0(%rdi), %r14
  movq 8(%rdi), %rbx
  movq 16(%rdi), %rbp
  mov %r13, %r12
  shr $2, %r13
  mov %r12, %rax
  add %r12, %r13
  jmp L1
.balign 16
L0:
  addq 0(%rsi), %r14
  adcq 8(%rsi), %rbx
  lea 16(%rsi), %rsi
  adc %rcx, %rbp
  mul %r14
  mov %rax, %r9
  mov %r11, %rax
  mov %rdx, %r10
  mul %r14
  mov %rax, %r14
  mov %r11, %rax
  mov %rdx, %r8
  mul %rbx
  add %rax, %r9
  mov %r13, %rax
  adc %rdx, %r10
  mul %rbx
  mov %rbp, %rbx
  add %rax, %r14
  adc %rdx, %r8
  imul %r13, %rbx
  add %rbx, %r9
  mov %r8, %rbx
  adc $0, %r10
  imul %r11, %rbp
  add %r9, %rbx
  mov $18446744073709551612, %rax
  adc %rbp, %r10
  and %r10, %rax
  mov %r10, %rbp
  shr $2, %r10
  and $3, %rbp
  add %r10, %rax
  add %rax, %r14
  adc $0, %rbx
  adc $0, %rbp
  mov %r12, %rax
  sub $1, %r15
.balign 16
L1:
  cmp $0, %r15
  jne L0
  movq %r14, 0(%rdi)
  movq %rbx, 8(%rdi)
  movq %rbp, 16(%rdi)
  movq 184(%rdi), %rax
  cmp $1, %rax
  jne L2
  movq 56(%rdi), %r15
  cmp $0, %r15
  je L4
  movq 32(%rdi), %rax
  movq 0(%rsi), %r8
  movq 8(%rsi), %r9
  cmp $8, %r15
  jae L6
  mov %r15, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  mov %rdx, %rcx
  sub $1, %rcx
  and %rcx, %r8
  mov $0, %r9
  add %r8, %r14
  adc %r9, %rbx
  adc $0, %rbp
  add %rdx, %r14
  adc $0, %rbx
  adc $0, %rbp
  jmp L7
L6:
  mov %r15, %rcx
  sub $8, %rcx
  shl $3, %rcx
  mov $1, %rdx
  shl %cl, %rdx
  mov %rdx, %rcx
  sub $1, %rcx
  and %rcx, %r9
  add %r8, %r14
  adc %r9, %rbx
  adc $0, %rbp
  add $0, %r14
  adc %rdx, %rbx
  adc $0, %rbp
L7:
  mul %r14
  mov %rax, %r9
  mov %r11, %rax
  mov %rdx, %r10
  mul %r14
  mov %rax, %r14
  mov %r11, %rax
  mov %rdx, %r8
  mul %rbx
  add %rax, %r9
  mov %r13, %rax
  adc %rdx, %r10
  mul %rbx
  mov %rbp, %rbx
  add %rax, %r14
  adc %rdx, %r8
  imul %r13, %rbx
  add %rbx, %r9
  mov %r8, %rbx
  adc $0, %r10
  imul %r11, %rbp
  add %r9, %rbx
  mov $18446744073709551612, %rax
  adc %rbp, %r10
  and %r10, %rax
  mov %r10, %rbp
  shr $2, %r10
  and $3, %rbp
  add %r10, %rax
  add %rax, %r14
  adc $0, %rbx
  adc $0, %rbp
  jmp L5
L4:
L5:
  mov %r14, %r8
  mov %rbx, %r9
  mov %rbp, %r10
  add $5, %r8
  adc $0, %r9
  adc $0, %r10
  shr $2, %r10
  mov %r10, %rax
  sub $1, %rax
  and %rax, %r14
  and %rax, %rbx
  mov $0, %rax
  sub %r10, %rax
  and %rax, %r8
  and %rax, %r9
  add %r8, %r14
  add %r9, %rbx
  movq 40(%rdi), %rax
  movq 48(%rdi), %rdx
  add %rax, %r14
  adc %rdx, %rbx
  jmp L3
L2:
L3:
  movq %r14, 0(%rdi)
  movq %rbx, 8(%rdi)
  movq %rbp, 16(%rdi)
  pop %r15
  pop %r14
  pop %r13
  pop %r12
  pop %rsi
  pop %rax
  pop %rbp
  pop %rbx
  mov %rax, %rdi
  ret


