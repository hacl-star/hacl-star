.code
ALIGN 16
add1 proc
  push rdi
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  xor r8, r8
  xor r9, r9
  xor r10, r10
  xor r11, r11
  xor rax, rax
  add rdx, qword ptr [rsi + 0]
  mov qword ptr [rdi + 0], rdx
  adcx r8, qword ptr [rsi + 8]
  mov qword ptr [rdi + 8], r8
  adcx r9, qword ptr [rsi + 16]
  mov qword ptr [rdi + 16], r9
  adcx r10, qword ptr [rsi + 24]
  mov qword ptr [rdi + 24], r10
  adcx rax, r11
  pop rsi
  pop rdi
  ret
add1 endp
ALIGN 16
fadd_ proc
  push rdi
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov r8, qword ptr [rdx + 0]
  add r8, qword ptr [rsi + 0]
  mov r9, qword ptr [rdx + 8]
  adcx r9, qword ptr [rsi + 8]
  mov r10, qword ptr [rdx + 16]
  adcx r10, qword ptr [rsi + 16]
  mov r11, qword ptr [rdx + 24]
  adcx r11, qword ptr [rsi + 24]
  mov rax, 0
  mov rdx, 38
  cmovc rax, rdx
  xor rcx, rcx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 8], r9
  adcx r10, rcx
  mov qword ptr [rdi + 16], r10
  adcx r11, rcx
  mov qword ptr [rdi + 24], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 0], r8
  pop rsi
  pop rdi
  ret
fadd_ endp
ALIGN 16
fsub_ proc
  push rdi
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov r8, qword ptr [rsi + 0]
  sub r8, qword ptr [rdx + 0]
  mov r9, qword ptr [rsi + 8]
  sbb r9, qword ptr [rdx + 8]
  mov r10, qword ptr [rsi + 16]
  sbb r10, qword ptr [rdx + 16]
  mov r11, qword ptr [rsi + 24]
  sbb r11, qword ptr [rdx + 24]
  mov rax, 0
  mov rcx, 38
  cmovc rax, rcx
  sub r8, rax
  sbb r9, 0
  sbb r10, 0
  sbb r11, 0
  mov rax, 0
  cmovc rax, rcx
  sub r8, rax
  mov qword ptr [rdi + 0], r8
  mov qword ptr [rdi + 8], r9
  mov qword ptr [rdi + 16], r10
  mov qword ptr [rdi + 24], r11
  pop rsi
  pop rdi
  ret
fsub_ endp
ALIGN 16
fmul1 proc
  push rdi
  push r12
  push r13
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mulx rcx, r8, qword ptr [rsi + 0]
  mulx r12, r9, qword ptr [rsi + 8]
  add r9, rcx
  mov rcx, 0
  mulx r13, r10, qword ptr [rsi + 16]
  adcx r10, r12
  mulx rax, r11, qword ptr [rsi + 24]
  adcx r11, r13
  adcx rax, rcx
  mov rdx, 38
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 8], r9
  adcx r10, rcx
  mov qword ptr [rdi + 16], r10
  adcx r11, rcx
  mov qword ptr [rdi + 24], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 0], r8
  pop rsi
  pop r13
  pop r12
  pop rdi
  ret
fmul1 endp
ALIGN 16
fmul_ proc
  push r12
  push r13
  push r14
  push r15
  push rsi
  push rdi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, r9
  mov r15, rdx
  mov rdx, qword ptr [rsi + 0]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  mov qword ptr [rdi + 0], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  mov qword ptr [rdi + 8], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  mov rax, 0
  adox rax, rdx
  mov rdx, qword ptr [rsi + 8]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  adcx r8, qword ptr [rdi + 8]
  mov qword ptr [rdi + 8], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 16], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  adcx r12, r14
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  adcx r14, rax
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov rdx, qword ptr [rsi + 16]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  adcx r8, qword ptr [rdi + 16]
  mov qword ptr [rdi + 16], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 24], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  adcx r12, r14
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  adcx r14, rax
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov rdx, qword ptr [rsi + 24]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  adcx r8, qword ptr [rdi + 24]
  mov qword ptr [rdi + 24], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 32], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  adcx r12, r14
  mov qword ptr [rdi + 40], r12
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  adcx r14, rax
  mov qword ptr [rdi + 48], r14
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov qword ptr [rdi + 56], rax
  mov rsi, rdi
  mov rdi, r15
  mov rdx, 38
  mulx r13, r8, qword ptr [rsi + 32]
  xor rcx, rcx
  adox r8, qword ptr [rsi + 0]
  mulx r12, r9, qword ptr [rsi + 40]
  adcx r9, r13
  adox r9, qword ptr [rsi + 8]
  mulx r13, r10, qword ptr [rsi + 48]
  adcx r10, r12
  adox r10, qword ptr [rsi + 16]
  mulx rax, r11, qword ptr [rsi + 56]
  adcx r11, r13
  adox r11, qword ptr [rsi + 24]
  adcx rax, rcx
  adox rax, rcx
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 8], r9
  adcx r10, rcx
  mov qword ptr [rdi + 16], r10
  adcx r11, rcx
  mov qword ptr [rdi + 24], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 0], r8
  pop rdi
  pop rsi
  pop r15
  pop r14
  pop r13
  pop r12
  ret
fmul_ endp
ALIGN 16
fmul2 proc
  push r12
  push r13
  push r14
  push r15
  push rsi
  push rdi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, r9
  mov r15, rdx
  mov rdx, qword ptr [rsi + 0]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  mov qword ptr [rdi + 0], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  mov qword ptr [rdi + 8], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  mov rax, 0
  adox rax, rdx
  mov rdx, qword ptr [rsi + 8]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  adcx r8, qword ptr [rdi + 8]
  mov qword ptr [rdi + 8], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 16], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  adcx r12, r14
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  adcx r14, rax
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov rdx, qword ptr [rsi + 16]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  adcx r8, qword ptr [rdi + 16]
  mov qword ptr [rdi + 16], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 24], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  adcx r12, r14
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  adcx r14, rax
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov rdx, qword ptr [rsi + 24]
  mulx r9, r8, qword ptr [rcx + 0]
  xor r10, r10
  adcx r8, qword ptr [rdi + 24]
  mov qword ptr [rdi + 24], r8
  mulx r11, r10, qword ptr [rcx + 8]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 32], r10
  mulx r13, r12, qword ptr [rcx + 16]
  adox r12, r11
  adcx r12, r14
  mov qword ptr [rdi + 40], r12
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 24]
  adox r14, r13
  adcx r14, rax
  mov qword ptr [rdi + 48], r14
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov qword ptr [rdi + 56], rax
  mov rdx, qword ptr [rsi + 32]
  mulx r9, r8, qword ptr [rcx + 32]
  xor r10, r10
  mov qword ptr [rdi + 64], r8
  mulx r11, r10, qword ptr [rcx + 40]
  adox r10, r9
  mov qword ptr [rdi + 72], r10
  mulx r13, r12, qword ptr [rcx + 48]
  adox r12, r11
  mulx rdx, r14, qword ptr [rcx + 56]
  adox r14, r13
  mov rax, 0
  adox rax, rdx
  mov rdx, qword ptr [rsi + 40]
  mulx r9, r8, qword ptr [rcx + 32]
  xor r10, r10
  adcx r8, qword ptr [rdi + 72]
  mov qword ptr [rdi + 72], r8
  mulx r11, r10, qword ptr [rcx + 40]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 80], r10
  mulx r13, r12, qword ptr [rcx + 48]
  adox r12, r11
  adcx r12, r14
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 56]
  adox r14, r13
  adcx r14, rax
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov rdx, qword ptr [rsi + 48]
  mulx r9, r8, qword ptr [rcx + 32]
  xor r10, r10
  adcx r8, qword ptr [rdi + 80]
  mov qword ptr [rdi + 80], r8
  mulx r11, r10, qword ptr [rcx + 40]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 88], r10
  mulx r13, r12, qword ptr [rcx + 48]
  adox r12, r11
  adcx r12, r14
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 56]
  adox r14, r13
  adcx r14, rax
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov rdx, qword ptr [rsi + 56]
  mulx r9, r8, qword ptr [rcx + 32]
  xor r10, r10
  adcx r8, qword ptr [rdi + 88]
  mov qword ptr [rdi + 88], r8
  mulx r11, r10, qword ptr [rcx + 40]
  adox r10, r9
  adcx r10, r12
  mov qword ptr [rdi + 96], r10
  mulx r13, r12, qword ptr [rcx + 48]
  adox r12, r11
  adcx r12, r14
  mov qword ptr [rdi + 104], r12
  mov r8, 0
  mulx rdx, r14, qword ptr [rcx + 56]
  adox r14, r13
  adcx r14, rax
  mov qword ptr [rdi + 112], r14
  mov rax, 0
  adox rax, rdx
  adcx rax, r8
  mov qword ptr [rdi + 120], rax
  mov rsi, rdi
  mov rdi, r15
  mov rdx, 38
  mulx r13, r8, qword ptr [rsi + 32]
  xor rcx, rcx
  adox r8, qword ptr [rsi + 0]
  mulx r12, r9, qword ptr [rsi + 40]
  adcx r9, r13
  adox r9, qword ptr [rsi + 8]
  mulx r13, r10, qword ptr [rsi + 48]
  adcx r10, r12
  adox r10, qword ptr [rsi + 16]
  mulx rax, r11, qword ptr [rsi + 56]
  adcx r11, r13
  adox r11, qword ptr [rsi + 24]
  adcx rax, rcx
  adox rax, rcx
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 8], r9
  adcx r10, rcx
  mov qword ptr [rdi + 16], r10
  adcx r11, rcx
  mov qword ptr [rdi + 24], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 0], r8
  mov rdx, 38
  mulx r13, r8, qword ptr [rsi + 96]
  xor rcx, rcx
  adox r8, qword ptr [rsi + 64]
  mulx r12, r9, qword ptr [rsi + 104]
  adcx r9, r13
  adox r9, qword ptr [rsi + 72]
  mulx r13, r10, qword ptr [rsi + 112]
  adcx r10, r12
  adox r10, qword ptr [rsi + 80]
  mulx rax, r11, qword ptr [rsi + 120]
  adcx r11, r13
  adox r11, qword ptr [rsi + 88]
  adcx rax, rcx
  adox rax, rcx
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 40], r9
  adcx r10, rcx
  mov qword ptr [rdi + 48], r10
  adcx r11, rcx
  mov qword ptr [rdi + 56], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 32], r8
  pop rdi
  pop rsi
  pop r15
  pop r14
  pop r13
  pop r12
  ret
fmul2 endp
ALIGN 16
fsqr proc
  push r15
  push r12
  push r13
  push r14
  push rbx
  push rsi
  push rdi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rbx, rdx
  mov rdx, qword ptr [rsi + 0]
  mulx r14, r8, qword ptr [rsi + 8]
  xor r15, r15
  mulx r10, r9, qword ptr [rsi + 16]
  adcx r9, r14
  mulx rcx, rax, qword ptr [rsi + 24]
  adcx r10, rax
  mov rdx, qword ptr [rsi + 24]
  mulx r12, r11, qword ptr [rsi + 8]
  adcx r11, rcx
  mulx r13, rax, qword ptr [rsi + 16]
  adcx r12, rax
  mov rdx, qword ptr [rsi + 8]
  adcx r13, r15
  mulx rcx, rax, qword ptr [rsi + 16]
  mov r14, 0
  xor r15, r15
  adox r10, rax
  adcx r8, r8
  adox r11, rcx
  adcx r9, r9
  adox r12, r15
  adcx r10, r10
  adox r13, r15
  adcx r11, r11
  adox r14, r15
  adcx r12, r12
  adcx r13, r13
  adcx r14, r14
  mov rdx, qword ptr [rsi + 0]
  mulx rcx, rax, rdx
  mov qword ptr [rdi + 0], rax
  add r8, rcx
  mov qword ptr [rdi + 8], r8
  mov rdx, qword ptr [rsi + 8]
  mulx rcx, rax, rdx
  adcx r9, rax
  mov qword ptr [rdi + 16], r9
  adcx r10, rcx
  mov qword ptr [rdi + 24], r10
  mov rdx, qword ptr [rsi + 16]
  mulx rcx, rax, rdx
  adcx r11, rax
  mov qword ptr [rdi + 32], r11
  adcx r12, rcx
  mov qword ptr [rdi + 40], r12
  mov rdx, qword ptr [rsi + 24]
  mulx rcx, rax, rdx
  adcx r13, rax
  mov qword ptr [rdi + 48], r13
  adcx r14, rcx
  mov qword ptr [rdi + 56], r14
  mov rsi, rdi
  mov rdi, rbx
  mov rdx, 38
  mulx r13, r8, qword ptr [rsi + 32]
  xor rcx, rcx
  adox r8, qword ptr [rsi + 0]
  mulx r12, r9, qword ptr [rsi + 40]
  adcx r9, r13
  adox r9, qword ptr [rsi + 8]
  mulx r13, r10, qword ptr [rsi + 48]
  adcx r10, r12
  adox r10, qword ptr [rsi + 16]
  mulx rax, r11, qword ptr [rsi + 56]
  adcx r11, r13
  adox r11, qword ptr [rsi + 24]
  adcx rax, rcx
  adox rax, rcx
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 8], r9
  adcx r10, rcx
  mov qword ptr [rdi + 16], r10
  adcx r11, rcx
  mov qword ptr [rdi + 24], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 0], r8
  pop rdi
  pop rsi
  pop rbx
  pop r14
  pop r13
  pop r12
  pop r15
  ret
fsqr endp
ALIGN 16
fsqr2 proc
  push r15
  push r12
  push r13
  push r14
  push rbx
  push rsi
  push rdi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rbx, rdx
  mov rdx, qword ptr [rsi + 0]
  mulx r14, r8, qword ptr [rsi + 8]
  xor r15, r15
  mulx r10, r9, qword ptr [rsi + 16]
  adcx r9, r14
  mulx rcx, rax, qword ptr [rsi + 24]
  adcx r10, rax
  mov rdx, qword ptr [rsi + 24]
  mulx r12, r11, qword ptr [rsi + 8]
  adcx r11, rcx
  mulx r13, rax, qword ptr [rsi + 16]
  adcx r12, rax
  mov rdx, qword ptr [rsi + 8]
  adcx r13, r15
  mulx rcx, rax, qword ptr [rsi + 16]
  mov r14, 0
  xor r15, r15
  adox r10, rax
  adcx r8, r8
  adox r11, rcx
  adcx r9, r9
  adox r12, r15
  adcx r10, r10
  adox r13, r15
  adcx r11, r11
  adox r14, r15
  adcx r12, r12
  adcx r13, r13
  adcx r14, r14
  mov rdx, qword ptr [rsi + 0]
  mulx rcx, rax, rdx
  mov qword ptr [rdi + 0], rax
  add r8, rcx
  mov qword ptr [rdi + 8], r8
  mov rdx, qword ptr [rsi + 8]
  mulx rcx, rax, rdx
  adcx r9, rax
  mov qword ptr [rdi + 16], r9
  adcx r10, rcx
  mov qword ptr [rdi + 24], r10
  mov rdx, qword ptr [rsi + 16]
  mulx rcx, rax, rdx
  adcx r11, rax
  mov qword ptr [rdi + 32], r11
  adcx r12, rcx
  mov qword ptr [rdi + 40], r12
  mov rdx, qword ptr [rsi + 24]
  mulx rcx, rax, rdx
  adcx r13, rax
  mov qword ptr [rdi + 48], r13
  adcx r14, rcx
  mov qword ptr [rdi + 56], r14
  mov rdx, qword ptr [rsi + 32]
  mulx r14, r8, qword ptr [rsi + 40]
  xor r15, r15
  mulx r10, r9, qword ptr [rsi + 48]
  adcx r9, r14
  mulx rcx, rax, qword ptr [rsi + 56]
  adcx r10, rax
  mov rdx, qword ptr [rsi + 56]
  mulx r12, r11, qword ptr [rsi + 40]
  adcx r11, rcx
  mulx r13, rax, qword ptr [rsi + 48]
  adcx r12, rax
  mov rdx, qword ptr [rsi + 40]
  adcx r13, r15
  mulx rcx, rax, qword ptr [rsi + 48]
  mov r14, 0
  xor r15, r15
  adox r10, rax
  adcx r8, r8
  adox r11, rcx
  adcx r9, r9
  adox r12, r15
  adcx r10, r10
  adox r13, r15
  adcx r11, r11
  adox r14, r15
  adcx r12, r12
  adcx r13, r13
  adcx r14, r14
  mov rdx, qword ptr [rsi + 32]
  mulx rcx, rax, rdx
  mov qword ptr [rdi + 64], rax
  add r8, rcx
  mov qword ptr [rdi + 72], r8
  mov rdx, qword ptr [rsi + 40]
  mulx rcx, rax, rdx
  adcx r9, rax
  mov qword ptr [rdi + 80], r9
  adcx r10, rcx
  mov qword ptr [rdi + 88], r10
  mov rdx, qword ptr [rsi + 48]
  mulx rcx, rax, rdx
  adcx r11, rax
  mov qword ptr [rdi + 96], r11
  adcx r12, rcx
  mov qword ptr [rdi + 104], r12
  mov rdx, qword ptr [rsi + 56]
  mulx rcx, rax, rdx
  adcx r13, rax
  mov qword ptr [rdi + 112], r13
  adcx r14, rcx
  mov qword ptr [rdi + 120], r14
  mov rsi, rdi
  mov rdi, rbx
  mov rdx, 38
  mulx r13, r8, qword ptr [rsi + 32]
  xor rcx, rcx
  adox r8, qword ptr [rsi + 0]
  mulx r12, r9, qword ptr [rsi + 40]
  adcx r9, r13
  adox r9, qword ptr [rsi + 8]
  mulx r13, r10, qword ptr [rsi + 48]
  adcx r10, r12
  adox r10, qword ptr [rsi + 16]
  mulx rax, r11, qword ptr [rsi + 56]
  adcx r11, r13
  adox r11, qword ptr [rsi + 24]
  adcx rax, rcx
  adox rax, rcx
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 8], r9
  adcx r10, rcx
  mov qword ptr [rdi + 16], r10
  adcx r11, rcx
  mov qword ptr [rdi + 24], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 0], r8
  mov rdx, 38
  mulx r13, r8, qword ptr [rsi + 96]
  xor rcx, rcx
  adox r8, qword ptr [rsi + 64]
  mulx r12, r9, qword ptr [rsi + 104]
  adcx r9, r13
  adox r9, qword ptr [rsi + 72]
  mulx r13, r10, qword ptr [rsi + 112]
  adcx r10, r12
  adox r10, qword ptr [rsi + 80]
  mulx rax, r11, qword ptr [rsi + 120]
  adcx r11, r13
  adox r11, qword ptr [rsi + 88]
  adcx rax, rcx
  adox rax, rcx
  imul rax, rdx
  add r8, rax
  adcx r9, rcx
  mov qword ptr [rdi + 40], r9
  adcx r10, rcx
  mov qword ptr [rdi + 48], r10
  adcx r11, rcx
  mov qword ptr [rdi + 56], r11
  mov rax, 0
  cmovc rax, rdx
  add r8, rax
  mov qword ptr [rdi + 32], r8
  pop rdi
  pop rsi
  pop rbx
  pop r14
  pop r13
  pop r12
  pop r15
  ret
fsqr2 endp
ALIGN 16
cswap2 proc
  push rdi
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  add rdi, 18446744073709551615
  mov r8, qword ptr [rsi + 0]
  mov r9, qword ptr [rdx + 0]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 0], r8
  mov qword ptr [rdx + 0], r9
  mov r8, qword ptr [rsi + 8]
  mov r9, qword ptr [rdx + 8]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 8], r8
  mov qword ptr [rdx + 8], r9
  mov r8, qword ptr [rsi + 16]
  mov r9, qword ptr [rdx + 16]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 16], r8
  mov qword ptr [rdx + 16], r9
  mov r8, qword ptr [rsi + 24]
  mov r9, qword ptr [rdx + 24]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 24], r8
  mov qword ptr [rdx + 24], r9
  mov r8, qword ptr [rsi + 32]
  mov r9, qword ptr [rdx + 32]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 32], r8
  mov qword ptr [rdx + 32], r9
  mov r8, qword ptr [rsi + 40]
  mov r9, qword ptr [rdx + 40]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 40], r8
  mov qword ptr [rdx + 40], r9
  mov r8, qword ptr [rsi + 48]
  mov r9, qword ptr [rdx + 48]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 48], r8
  mov qword ptr [rdx + 48], r9
  mov r8, qword ptr [rsi + 56]
  mov r9, qword ptr [rdx + 56]
  mov r10, r8
  cmovc r8, r9
  cmovc r9, r10
  mov qword ptr [rsi + 56], r8
  mov qword ptr [rdx + 56], r9
  pop rsi
  pop rdi
  ret
cswap2 endp
end
