.code
ALIGN 16
x64_poly1305 proc
  mov rax, rdi
  mov r11, rsi
  mov rdi, rcx
  mov rsi, rdx
  mov rdx, r8
  mov rcx, r9
  mov qword ptr [rdi + 184], rcx
  push rbx
  push rbp
  push rax
  push r11
  push r12
  push r13
  push r14
  push r15
  mov r11, qword ptr [rdi + 24]
  mov r12, qword ptr [rdi + 32]
  mov rcx, 1152921487695413247
  and r11, rcx
  mov rcx, 1152921487695413244
  and r12, rcx
  mov qword ptr [rdi + 24], r11
  mov qword ptr [rdi + 32], r12
  mov rax, rdx
  and rax, 15
  sub rdx, rax
  mov qword ptr [rdi + 56], rax
  mov qword ptr [rdi + 64], rdx
  mov rcx, 1
  shr rdx, 4
  mov r15, rdx
  mov r11, qword ptr [rdi + 24]
  mov r13, qword ptr [rdi + 32]
  mov r14, qword ptr [rdi + 0]
  mov rbx, qword ptr [rdi + 8]
  mov rbp, qword ptr [rdi + 16]
  mov r12, r13
  shr r13, 2
  mov rax, r12
  add r13, r12
  jmp L1
ALIGN 16
L0:
  add r14, qword ptr [rsi + 0]
  adc rbx, qword ptr [rsi + 8]
  lea rsi, qword ptr [rsi + 16]
  adc rbp, rcx
  mul r14
  mov r9, rax
  mov rax, r11
  mov r10, rdx
  mul r14
  mov r14, rax
  mov rax, r11
  mov r8, rdx
  mul rbx
  add r9, rax
  mov rax, r13
  adc r10, rdx
  mul rbx
  mov rbx, rbp
  add r14, rax
  adc r8, rdx
  imul rbx, r13
  add r9, rbx
  mov rbx, r8
  adc r10, 0
  imul rbp, r11
  add rbx, r9
  mov rax, 18446744073709551612
  adc r10, rbp
  and rax, r10
  mov rbp, r10
  shr r10, 2
  and rbp, 3
  add rax, r10
  add r14, rax
  adc rbx, 0
  adc rbp, 0
  mov rax, r12
  sub r15, 1
ALIGN 16
L1:
  cmp r15, 0
  jne L0
  mov qword ptr [rdi + 0], r14
  mov qword ptr [rdi + 8], rbx
  mov qword ptr [rdi + 16], rbp
  mov rax, qword ptr [rdi + 184]
  cmp rax, 1
  jne L2
  mov r15, qword ptr [rdi + 56]
  cmp r15, 0
  je L4
  mov rax, qword ptr [rdi + 32]
  mov r8, qword ptr [rsi + 0]
  mov r9, qword ptr [rsi + 8]
  cmp r15, 8
  jae L6
  mov rcx, r15
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  mov rcx, rdx
  sub rcx, 1
  and r8, rcx
  mov r9, 0
  add r14, r8
  adc rbx, r9
  adc rbp, 0
  add r14, rdx
  adc rbx, 0
  adc rbp, 0
  jmp L7
L6:
  mov rcx, r15
  sub rcx, 8
  shl rcx, 3
  mov rdx, 1
  shl rdx, cl
  mov rcx, rdx
  sub rcx, 1
  and r9, rcx
  add r14, r8
  adc rbx, r9
  adc rbp, 0
  add r14, 0
  adc rbx, rdx
  adc rbp, 0
L7:
  mul r14
  mov r9, rax
  mov rax, r11
  mov r10, rdx
  mul r14
  mov r14, rax
  mov rax, r11
  mov r8, rdx
  mul rbx
  add r9, rax
  mov rax, r13
  adc r10, rdx
  mul rbx
  mov rbx, rbp
  add r14, rax
  adc r8, rdx
  imul rbx, r13
  add r9, rbx
  mov rbx, r8
  adc r10, 0
  imul rbp, r11
  add rbx, r9
  mov rax, 18446744073709551612
  adc r10, rbp
  and rax, r10
  mov rbp, r10
  shr r10, 2
  and rbp, 3
  add rax, r10
  add r14, rax
  adc rbx, 0
  adc rbp, 0
  jmp L5
L4:
L5:
  mov r8, r14
  mov r9, rbx
  mov r10, rbp
  add r8, 5
  adc r9, 0
  adc r10, 0
  shr r10, 2
  mov rax, r10
  sub rax, 1
  and r14, rax
  and rbx, rax
  mov rax, 0
  sub rax, r10
  and r8, rax
  and r9, rax
  add r14, r8
  add rbx, r9
  mov rax, qword ptr [rdi + 40]
  mov rdx, qword ptr [rdi + 48]
  add r14, rax
  adc rbx, rdx
  jmp L3
L2:
L3:
  mov qword ptr [rdi + 0], r14
  mov qword ptr [rdi + 8], rbx
  mov qword ptr [rdi + 16], rbp
  pop r15
  pop r14
  pop r13
  pop r12
  pop rsi
  pop rax
  pop rbp
  pop rbx
  mov rdi, rax
  ret
x64_poly1305 endp
end
