.text
.global mul
mul:
  push %rsi
  push %r12
  push %r13
  push %r14
  mov %rdx, %rcx
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
  pop %r14
  pop %r13
  pop %r12
  pop %rsi
  ret

.global sqr
sqr:
  push %r15
  push %rsi
  push %r12
  push %r13
  push %r14
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
  pop %r14
  pop %r13
  pop %r12
  pop %rsi
  pop %r15
  ret

.global mul1
mul1:
  push %rsi
  push %r12
  push %r13
  push %r14
  mulxq 0(%rsi), %r8, %r9
  movq %r8, 0(%rdi)
  xor %r8, %r8
  mulxq 8(%rsi), %r10, %r11
  add %r9, %r10
  movq %r10, 8(%rdi)
  mulxq 16(%rsi), %r12, %r13
  adcx %r11, %r12
  movq %r12, 16(%rdi)
  mulxq 24(%rsi), %r14, %rax
  adcx %r13, %r14
  movq %r14, 24(%rdi)
  adcx %r8, %rax
  pop %r14
  pop %r13
  pop %r12
  pop %rsi
  ret

.global add1
add1:
  push %rsi
  mov %rdx, %rcx
  xor %r8, %r8
  xor %r9, %r9
  xor %r10, %r10
  xor %r11, %r11
  xor %rax, %rax
  addq 0(%rsi), %rcx
  movq %rcx, 0(%rdi)
  adcxq 8(%rsi), %r8
  movq %r8, 8(%rdi)
  adcxq 16(%rsi), %r9
  movq %r9, 16(%rdi)
  adcxq 24(%rsi), %r10
  movq %r10, 24(%rdi)
  adcx %r11, %rax
  pop %rsi
  ret

.global add
add:
  push %rsi
  push %r12
  mov %rdx, %rcx
  xor %r8, %r8
  xor %rax, %rax
  movq 0(%rcx), %r9
  addq 0(%rsi), %r9
  movq %r9, 0(%rdi)
  movq 8(%rcx), %r10
  adcxq 8(%rsi), %r10
  movq %r10, 8(%rdi)
  movq 16(%rcx), %r11
  adcxq 16(%rsi), %r11
  movq %r11, 16(%rdi)
  movq 24(%rcx), %r12
  adcxq 24(%rsi), %r12
  movq %r12, 24(%rdi)
  adcx %r8, %rax
  pop %r12
  pop %rsi
  ret

.global sub1
sub1:
  push %rsi
  mov %rdx, %rcx
  xor %r8, %r8
  xor %r9, %r9
  xor %r10, %r10
  xor %r11, %r11
  xor %rax, %rax
  movq 0(%rsi), %r8
  sub %rcx, %r8
  movq %r8, 0(%rdi)
  movq 8(%rsi), %r9
  sbb %r10, %r9
  movq %r9, 8(%rdi)
  movq 16(%rsi), %r10
  sbb %r11, %r10
  movq %r10, 16(%rdi)
  movq 24(%rsi), %r11
  sbb %rax, %r11
  movq %r11, 24(%rdi)
  adc %rax, %rax
  pop %rsi
  ret

.global sub
sub:
  push %rsi
  push %r12
  mov %rdx, %rcx
  xor %rax, %rax
  movq 0(%rsi), %r8
  subq 0(%rcx), %r8
  movq %r8, 0(%rdi)
  movq 8(%rsi), %r9
  sbbq 8(%rcx), %r9
  movq %r9, 8(%rdi)
  movq 16(%rsi), %r10
  sbbq 16(%rcx), %r10
  movq %r10, 16(%rdi)
  movq 24(%rsi), %r11
  sbbq 24(%rcx), %r11
  movq %r11, 24(%rdi)
  adc %rax, %rax
  pop %r12
  pop %rsi
  ret


