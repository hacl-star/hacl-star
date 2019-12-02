.text
.global add1
add1:
  push %rdi
  push %rsi
  xor %r8, %r8
  xor %r9, %r9
  xor %r10, %r10
  xor %r11, %r11
  xor %rax, %rax
  addq 0(%rsi), %rdx
  movq %rdx, 0(%rdi)
  adcxq 8(%rsi), %r8
  movq %r8, 8(%rdi)
  adcxq 16(%rsi), %r9
  movq %r9, 16(%rdi)
  adcxq 24(%rsi), %r10
  movq %r10, 24(%rdi)
  adcx %r11, %rax
  pop %rsi
  pop %rdi
  ret

.global fadd_
fadd_:
  movq 0(%rdx), %r8
  addq 0(%rsi), %r8
  movq 8(%rdx), %r9
  adcxq 8(%rsi), %r9
  movq 16(%rdx), %r10
  adcxq 16(%rsi), %r10
  movq 24(%rdx), %r11
  adcxq 24(%rsi), %r11
  mov $0, %rax
  mov $38, %rdx
  cmovc %rdx, %rax
  xor %rcx, %rcx
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 8(%rdi)
  adcx %rcx, %r10
  movq %r10, 16(%rdi)
  adcx %rcx, %r11
  movq %r11, 24(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 0(%rdi)
  ret

.global fsub_
fsub_:
  movq 0(%rsi), %r8
  subq 0(%rdx), %r8
  movq 8(%rsi), %r9
  sbbq 8(%rdx), %r9
  movq 16(%rsi), %r10
  sbbq 16(%rdx), %r10
  movq 24(%rsi), %r11
  sbbq 24(%rdx), %r11
  mov $0, %rax
  mov $38, %rcx
  cmovc %rcx, %rax
  sub %rax, %r8
  sbb $0, %r9
  sbb $0, %r10
  sbb $0, %r11
  mov $0, %rax
  cmovc %rcx, %rax
  sub %rax, %r8
  movq %r8, 0(%rdi)
  movq %r9, 8(%rdi)
  movq %r10, 16(%rdi)
  movq %r11, 24(%rdi)
  ret

.global fmul1
fmul1:
  push %rdi
  push %r12
  push %r13
  mulxq 0(%rsi), %r8, %rcx
  mulxq 8(%rsi), %r9, %r12
  add %rcx, %r9
  mov $0, %rcx
  mulxq 16(%rsi), %r10, %r13
  adcx %r12, %r10
  mulxq 24(%rsi), %r11, %rax
  adcx %r13, %r11
  adcx %rcx, %rax
  mov $38, %rdx
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 8(%rdi)
  adcx %rcx, %r10
  movq %r10, 16(%rdi)
  adcx %rcx, %r11
  movq %r11, 24(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 0(%rdi)
  pop %r13
  pop %r12
  pop %rdi
  ret

.global fmul_
fmul_:
  push %r12
  push %r13
  push %r14
  push %r15
  mov %rdx, %r15
  movq 0(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  movq %r8, 0(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  movq %r10, 8(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  mov $0, %rax
  adox %rdx, %rax
  movq 8(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 8(%rdi), %r8
  movq %r8, 8(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 16(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  mov $0, %r8
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq 16(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 16(%rdi), %r8
  movq %r8, 16(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 24(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  mov $0, %r8
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq 24(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 24(%rdi), %r8
  movq %r8, 24(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 32(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  movq %r12, 40(%rdi)
  mov $0, %r8
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  movq %r14, 48(%rdi)
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq %rax, 56(%rdi)
  mov %rdi, %rsi
  mov %r15, %rdi
  mov $38, %rdx
  mulxq 32(%rsi), %r8, %r13
  xor %rcx, %rcx
  adoxq 0(%rsi), %r8
  mulxq 40(%rsi), %r9, %r12
  adcx %r13, %r9
  adoxq 8(%rsi), %r9
  mulxq 48(%rsi), %r10, %r13
  adcx %r12, %r10
  adoxq 16(%rsi), %r10
  mulxq 56(%rsi), %r11, %rax
  adcx %r13, %r11
  adoxq 24(%rsi), %r11
  adcx %rcx, %rax
  adox %rcx, %rax
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 8(%rdi)
  adcx %rcx, %r10
  movq %r10, 16(%rdi)
  adcx %rcx, %r11
  movq %r11, 24(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 0(%rdi)
  pop %r15
  pop %r14
  pop %r13
  pop %r12
  ret

.global fmul2
fmul2:
  push %r12
  push %r13
  push %r14
  push %r15
  mov %rdx, %r15
  movq 0(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  movq %r8, 0(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  movq %r10, 8(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  mov $0, %rax
  adox %rdx, %rax
  movq 8(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 8(%rdi), %r8
  movq %r8, 8(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 16(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  mov $0, %r8
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq 16(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 16(%rdi), %r8
  movq %r8, 16(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 24(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  mov $0, %r8
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq 24(%rsi), %rdx
  mulxq 0(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 24(%rdi), %r8
  movq %r8, 24(%rdi)
  mulxq 8(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 32(%rdi)
  mulxq 16(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  movq %r12, 40(%rdi)
  mov $0, %r8
  mulxq 24(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  movq %r14, 48(%rdi)
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq %rax, 56(%rdi)
  movq 32(%rsi), %rdx
  mulxq 32(%rcx), %r8, %r9
  xor %r10, %r10
  movq %r8, 64(%rdi)
  mulxq 40(%rcx), %r10, %r11
  adox %r9, %r10
  movq %r10, 72(%rdi)
  mulxq 48(%rcx), %r12, %r13
  adox %r11, %r12
  mulxq 56(%rcx), %r14, %rdx
  adox %r13, %r14
  mov $0, %rax
  adox %rdx, %rax
  movq 40(%rsi), %rdx
  mulxq 32(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 72(%rdi), %r8
  movq %r8, 72(%rdi)
  mulxq 40(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 80(%rdi)
  mulxq 48(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  mov $0, %r8
  mulxq 56(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq 48(%rsi), %rdx
  mulxq 32(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 80(%rdi), %r8
  movq %r8, 80(%rdi)
  mulxq 40(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 88(%rdi)
  mulxq 48(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  mov $0, %r8
  mulxq 56(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq 56(%rsi), %rdx
  mulxq 32(%rcx), %r8, %r9
  xor %r10, %r10
  adcxq 88(%rdi), %r8
  movq %r8, 88(%rdi)
  mulxq 40(%rcx), %r10, %r11
  adox %r9, %r10
  adcx %r12, %r10
  movq %r10, 96(%rdi)
  mulxq 48(%rcx), %r12, %r13
  adox %r11, %r12
  adcx %r14, %r12
  movq %r12, 104(%rdi)
  mov $0, %r8
  mulxq 56(%rcx), %r14, %rdx
  adox %r13, %r14
  adcx %rax, %r14
  movq %r14, 112(%rdi)
  mov $0, %rax
  adox %rdx, %rax
  adcx %r8, %rax
  movq %rax, 120(%rdi)
  mov %rdi, %rsi
  mov %r15, %rdi
  mov $38, %rdx
  mulxq 32(%rsi), %r8, %r13
  xor %rcx, %rcx
  adoxq 0(%rsi), %r8
  mulxq 40(%rsi), %r9, %r12
  adcx %r13, %r9
  adoxq 8(%rsi), %r9
  mulxq 48(%rsi), %r10, %r13
  adcx %r12, %r10
  adoxq 16(%rsi), %r10
  mulxq 56(%rsi), %r11, %rax
  adcx %r13, %r11
  adoxq 24(%rsi), %r11
  adcx %rcx, %rax
  adox %rcx, %rax
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 8(%rdi)
  adcx %rcx, %r10
  movq %r10, 16(%rdi)
  adcx %rcx, %r11
  movq %r11, 24(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 0(%rdi)
  mov $38, %rdx
  mulxq 96(%rsi), %r8, %r13
  xor %rcx, %rcx
  adoxq 64(%rsi), %r8
  mulxq 104(%rsi), %r9, %r12
  adcx %r13, %r9
  adoxq 72(%rsi), %r9
  mulxq 112(%rsi), %r10, %r13
  adcx %r12, %r10
  adoxq 80(%rsi), %r10
  mulxq 120(%rsi), %r11, %rax
  adcx %r13, %r11
  adoxq 88(%rsi), %r11
  adcx %rcx, %rax
  adox %rcx, %rax
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 40(%rdi)
  adcx %rcx, %r10
  movq %r10, 48(%rdi)
  adcx %rcx, %r11
  movq %r11, 56(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 32(%rdi)
  pop %r15
  pop %r14
  pop %r13
  pop %r12
  ret

.global fsqr
fsqr:
  push %r15
  push %r12
  push %r13
  push %r14
  push %rbx
  mov %rdx, %rbx
  movq 0(%rsi), %rdx
  mulxq 8(%rsi), %r8, %r14
  xor %r15, %r15
  mulxq 16(%rsi), %r9, %r10
  adcx %r14, %r9
  mulxq 24(%rsi), %rax, %rcx
  adcx %rax, %r10
  movq 24(%rsi), %rdx
  mulxq 8(%rsi), %r11, %r12
  adcx %rcx, %r11
  mulxq 16(%rsi), %rax, %r13
  adcx %rax, %r12
  movq 8(%rsi), %rdx
  adcx %r15, %r13
  mulxq 16(%rsi), %rax, %rcx
  mov $0, %r14
  xor %r15, %r15
  adox %rax, %r10
  adcx %r8, %r8
  adox %rcx, %r11
  adcx %r9, %r9
  adox %r15, %r12
  adcx %r10, %r10
  adox %r15, %r13
  adcx %r11, %r11
  adox %r15, %r14
  adcx %r12, %r12
  adcx %r13, %r13
  adcx %r14, %r14
  movq 0(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  movq %rax, 0(%rdi)
  add %rcx, %r8
  movq %r8, 8(%rdi)
  movq 8(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r9
  movq %r9, 16(%rdi)
  adcx %rcx, %r10
  movq %r10, 24(%rdi)
  movq 16(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r11
  movq %r11, 32(%rdi)
  adcx %rcx, %r12
  movq %r12, 40(%rdi)
  movq 24(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r13
  movq %r13, 48(%rdi)
  adcx %rcx, %r14
  movq %r14, 56(%rdi)
  mov %rdi, %rsi
  mov %rbx, %rdi
  mov $38, %rdx
  mulxq 32(%rsi), %r8, %r13
  xor %rcx, %rcx
  adoxq 0(%rsi), %r8
  mulxq 40(%rsi), %r9, %r12
  adcx %r13, %r9
  adoxq 8(%rsi), %r9
  mulxq 48(%rsi), %r10, %r13
  adcx %r12, %r10
  adoxq 16(%rsi), %r10
  mulxq 56(%rsi), %r11, %rax
  adcx %r13, %r11
  adoxq 24(%rsi), %r11
  adcx %rcx, %rax
  adox %rcx, %rax
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 8(%rdi)
  adcx %rcx, %r10
  movq %r10, 16(%rdi)
  adcx %rcx, %r11
  movq %r11, 24(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 0(%rdi)
  pop %rbx
  pop %r14
  pop %r13
  pop %r12
  pop %r15
  ret

.global fsqr2
fsqr2:
  push %r15
  push %r12
  push %r13
  push %r14
  push %rbx
  mov %rdx, %rbx
  movq 0(%rsi), %rdx
  mulxq 8(%rsi), %r8, %r14
  xor %r15, %r15
  mulxq 16(%rsi), %r9, %r10
  adcx %r14, %r9
  mulxq 24(%rsi), %rax, %rcx
  adcx %rax, %r10
  movq 24(%rsi), %rdx
  mulxq 8(%rsi), %r11, %r12
  adcx %rcx, %r11
  mulxq 16(%rsi), %rax, %r13
  adcx %rax, %r12
  movq 8(%rsi), %rdx
  adcx %r15, %r13
  mulxq 16(%rsi), %rax, %rcx
  mov $0, %r14
  xor %r15, %r15
  adox %rax, %r10
  adcx %r8, %r8
  adox %rcx, %r11
  adcx %r9, %r9
  adox %r15, %r12
  adcx %r10, %r10
  adox %r15, %r13
  adcx %r11, %r11
  adox %r15, %r14
  adcx %r12, %r12
  adcx %r13, %r13
  adcx %r14, %r14
  movq 0(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  movq %rax, 0(%rdi)
  add %rcx, %r8
  movq %r8, 8(%rdi)
  movq 8(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r9
  movq %r9, 16(%rdi)
  adcx %rcx, %r10
  movq %r10, 24(%rdi)
  movq 16(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r11
  movq %r11, 32(%rdi)
  adcx %rcx, %r12
  movq %r12, 40(%rdi)
  movq 24(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r13
  movq %r13, 48(%rdi)
  adcx %rcx, %r14
  movq %r14, 56(%rdi)
  movq 32(%rsi), %rdx
  mulxq 40(%rsi), %r8, %r14
  xor %r15, %r15
  mulxq 48(%rsi), %r9, %r10
  adcx %r14, %r9
  mulxq 56(%rsi), %rax, %rcx
  adcx %rax, %r10
  movq 56(%rsi), %rdx
  mulxq 40(%rsi), %r11, %r12
  adcx %rcx, %r11
  mulxq 48(%rsi), %rax, %r13
  adcx %rax, %r12
  movq 40(%rsi), %rdx
  adcx %r15, %r13
  mulxq 48(%rsi), %rax, %rcx
  mov $0, %r14
  xor %r15, %r15
  adox %rax, %r10
  adcx %r8, %r8
  adox %rcx, %r11
  adcx %r9, %r9
  adox %r15, %r12
  adcx %r10, %r10
  adox %r15, %r13
  adcx %r11, %r11
  adox %r15, %r14
  adcx %r12, %r12
  adcx %r13, %r13
  adcx %r14, %r14
  movq 32(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  movq %rax, 64(%rdi)
  add %rcx, %r8
  movq %r8, 72(%rdi)
  movq 40(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r9
  movq %r9, 80(%rdi)
  adcx %rcx, %r10
  movq %r10, 88(%rdi)
  movq 48(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r11
  movq %r11, 96(%rdi)
  adcx %rcx, %r12
  movq %r12, 104(%rdi)
  movq 56(%rsi), %rdx
  mulx %rdx, %rax, %rcx
  adcx %rax, %r13
  movq %r13, 112(%rdi)
  adcx %rcx, %r14
  movq %r14, 120(%rdi)
  mov %rdi, %rsi
  mov %rbx, %rdi
  mov $38, %rdx
  mulxq 32(%rsi), %r8, %r13
  xor %rcx, %rcx
  adoxq 0(%rsi), %r8
  mulxq 40(%rsi), %r9, %r12
  adcx %r13, %r9
  adoxq 8(%rsi), %r9
  mulxq 48(%rsi), %r10, %r13
  adcx %r12, %r10
  adoxq 16(%rsi), %r10
  mulxq 56(%rsi), %r11, %rax
  adcx %r13, %r11
  adoxq 24(%rsi), %r11
  adcx %rcx, %rax
  adox %rcx, %rax
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 8(%rdi)
  adcx %rcx, %r10
  movq %r10, 16(%rdi)
  adcx %rcx, %r11
  movq %r11, 24(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 0(%rdi)
  mov $38, %rdx
  mulxq 96(%rsi), %r8, %r13
  xor %rcx, %rcx
  adoxq 64(%rsi), %r8
  mulxq 104(%rsi), %r9, %r12
  adcx %r13, %r9
  adoxq 72(%rsi), %r9
  mulxq 112(%rsi), %r10, %r13
  adcx %r12, %r10
  adoxq 80(%rsi), %r10
  mulxq 120(%rsi), %r11, %rax
  adcx %r13, %r11
  adoxq 88(%rsi), %r11
  adcx %rcx, %rax
  adox %rcx, %rax
  imul %rdx, %rax
  add %rax, %r8
  adcx %rcx, %r9
  movq %r9, 40(%rdi)
  adcx %rcx, %r10
  movq %r10, 48(%rdi)
  adcx %rcx, %r11
  movq %r11, 56(%rdi)
  mov $0, %rax
  cmovc %rdx, %rax
  add %rax, %r8
  movq %r8, 32(%rdi)
  pop %rbx
  pop %r14
  pop %r13
  pop %r12
  pop %r15
  ret

.global cswap2
cswap2:
  add $18446744073709551615, %rdi
  movq 0(%rsi), %r8
  movq 0(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 0(%rsi)
  movq %r9, 0(%rdx)
  movq 8(%rsi), %r8
  movq 8(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 8(%rsi)
  movq %r9, 8(%rdx)
  movq 16(%rsi), %r8
  movq 16(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 16(%rsi)
  movq %r9, 16(%rdx)
  movq 24(%rsi), %r8
  movq 24(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 24(%rsi)
  movq %r9, 24(%rdx)
  movq 32(%rsi), %r8
  movq 32(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 32(%rsi)
  movq %r9, 32(%rdx)
  movq 40(%rsi), %r8
  movq 40(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 40(%rsi)
  movq %r9, 40(%rdx)
  movq 48(%rsi), %r8
  movq 48(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 48(%rsi)
  movq %r9, 48(%rdx)
  movq 56(%rsi), %r8
  movq 56(%rdx), %r9
  mov %r8, %r10
  cmovc %r9, %r8
  cmovc %r10, %r9
  movq %r8, 56(%rsi)
  movq %r9, 56(%rdx)
  ret


