.code
ALIGN 16
mul proc
  push rsi
  push r12
  push r13
  push r14
  mov rdi, rcx
  mov rsi, rdx
  mov rcx, r8
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
  pop r14
  pop r13
  pop r12
  pop rsi
  ret
mul endp
ALIGN 16
sqr proc
  push r15
  push rsi
  push r12
  push r13
  push r14
  mov rdi, rcx
  mov rsi, rdx
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
  pop r14
  pop r13
  pop r12
  pop rsi
  pop r15
  ret
sqr endp
ALIGN 16
mul1 proc
  push rsi
  push r12
  push r13
  push r14
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mulx r9, r8, qword ptr [rsi + 0]
  mov qword ptr [rdi + 0], r8
  xor r8, r8
  mulx r11, r10, qword ptr [rsi + 8]
  add r10, r9
  mov qword ptr [rdi + 8], r10
  mulx r13, r12, qword ptr [rsi + 16]
  adcx r12, r11
  mov qword ptr [rdi + 16], r12
  mulx rax, r14, qword ptr [rsi + 24]
  adcx r14, r13
  mov qword ptr [rdi + 24], r14
  adcx rax, r8
  pop r14
  pop r13
  pop r12
  pop rsi
  ret
mul1 endp
ALIGN 16
add1 proc
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, rdx
  xor r8, r8
  xor r9, r9
  xor r10, r10
  xor r11, r11
  xor rax, rax
  add rcx, qword ptr [rsi + 0]
  mov qword ptr [rdi + 0], rcx
  adcx r8, qword ptr [rsi + 8]
  mov qword ptr [rdi + 8], r8
  adcx r9, qword ptr [rsi + 16]
  mov qword ptr [rdi + 16], r9
  adcx r10, qword ptr [rsi + 24]
  mov qword ptr [rdi + 24], r10
  adcx rax, r11
  pop rsi
  ret
add1 endp
ALIGN 16
add proc
  push rsi
  push r12
  mov rdi, rcx
  mov rsi, rdx
  mov rcx, r8
  xor r8, r8
  xor rax, rax
  mov r9, qword ptr [rcx + 0]
  add r9, qword ptr [rsi + 0]
  mov qword ptr [rdi + 0], r9
  mov r10, qword ptr [rcx + 8]
  adcx r10, qword ptr [rsi + 8]
  mov qword ptr [rdi + 8], r10
  mov r11, qword ptr [rcx + 16]
  adcx r11, qword ptr [rsi + 16]
  mov qword ptr [rdi + 16], r11
  mov r12, qword ptr [rcx + 24]
  adcx r12, qword ptr [rsi + 24]
  mov qword ptr [rdi + 24], r12
  adcx rax, r8
  pop r12
  pop rsi
  ret
add endp
ALIGN 16
sub1 proc
  push rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, rdx
  xor r8, r8
  xor r9, r9
  xor r10, r10
  xor r11, r11
  xor rax, rax
  mov r8, qword ptr [rsi + 0]
  sub r8, rcx
  mov qword ptr [rdi + 0], r8
  mov r9, qword ptr [rsi + 8]
  sbb r9, r10
  mov qword ptr [rdi + 8], r9
  mov r10, qword ptr [rsi + 16]
  sbb r10, r11
  mov qword ptr [rdi + 16], r10
  mov r11, qword ptr [rsi + 24]
  sbb r11, rax
  mov qword ptr [rdi + 24], r11
  adc rax, rax
  pop rsi
  ret
sub1 endp
ALIGN 16
sub proc
  push rsi
  push r12
  mov rdi, rcx
  mov rsi, rdx
  mov rcx, r8
  xor rax, rax
  mov r8, qword ptr [rsi + 0]
  sub r8, qword ptr [rcx + 0]
  mov qword ptr [rdi + 0], r8
  mov r9, qword ptr [rsi + 8]
  sbb r9, qword ptr [rcx + 8]
  mov qword ptr [rdi + 8], r9
  mov r10, qword ptr [rsi + 16]
  sbb r10, qword ptr [rcx + 16]
  mov qword ptr [rdi + 16], r10
  mov r11, qword ptr [rsi + 24]
  sbb r11, qword ptr [rcx + 24]
  mov qword ptr [rdi + 24], r11
  adc rax, rax
  pop r12
  pop rsi
  ret
sub endp
end
