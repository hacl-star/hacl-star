.code
ALIGN 16
sha256_main_i_SHA256_Compute64Steps proc
  mov r9, rdx
  mov qword ptr [rsp + 100], rcx
  mov r8d, 0
  mov r11d, 0
  mov r11d, dword ptr [rcx + 0]
  mov r8d, dword ptr [rcx + 4]
  mov dword ptr [rsp + 44], r8d
  mov r8d, dword ptr [rcx + 8]
  mov dword ptr [rsp + 48], r8d
  mov r8d, dword ptr [rcx + 12]
  mov dword ptr [rsp + 52], r8d
  mov r8d, dword ptr [rcx + 16]
  mov dword ptr [rsp + 56], r8d
  mov r8d, dword ptr [rcx + 20]
  mov dword ptr [rsp + 60], r8d
  mov r8d, dword ptr [rcx + 24]
  mov dword ptr [rsp + 64], r8d
  mov r8d, dword ptr [rcx + 28]
  mov dword ptr [rsp + 68], r8d
  mov eax, 0
  mov ecx, 0
  mov edx, 0
  mov r10d, 0
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1116352408
  mov ecx, dword ptr [r9 + 0]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1899447441
  mov ecx, dword ptr [r9 + 4]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3049323471
  mov ecx, dword ptr [r9 + 8]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3921009573
  mov ecx, dword ptr [r9 + 12]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 961987163
  mov ecx, dword ptr [r9 + 16]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1508970993
  mov ecx, dword ptr [r9 + 20]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2453635748
  mov ecx, dword ptr [r9 + 24]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2870763221
  mov ecx, dword ptr [r9 + 28]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3624381080
  mov ecx, dword ptr [r9 + 32]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 310598401
  mov ecx, dword ptr [r9 + 36]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 607225278
  mov ecx, dword ptr [r9 + 40]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1426881987
  mov ecx, dword ptr [r9 + 44]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1925078388
  mov ecx, dword ptr [r9 + 48]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2162078206
  mov ecx, dword ptr [r9 + 52]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2614888103
  mov ecx, dword ptr [r9 + 56]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3248222580
  mov ecx, dword ptr [r9 + 60]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3835390401
  mov ecx, dword ptr [r9 + 64]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 4022224774
  mov ecx, dword ptr [r9 + 68]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 264347078
  mov ecx, dword ptr [r9 + 72]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 604807628
  mov ecx, dword ptr [r9 + 76]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 770255983
  mov ecx, dword ptr [r9 + 80]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1249150122
  mov ecx, dword ptr [r9 + 84]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1555081692
  mov ecx, dword ptr [r9 + 88]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1996064986
  mov ecx, dword ptr [r9 + 92]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2554220882
  mov ecx, dword ptr [r9 + 96]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2821834349
  mov ecx, dword ptr [r9 + 100]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2952996808
  mov ecx, dword ptr [r9 + 104]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3210313671
  mov ecx, dword ptr [r9 + 108]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3336571891
  mov ecx, dword ptr [r9 + 112]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3584528711
  mov ecx, dword ptr [r9 + 116]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 113926993
  mov ecx, dword ptr [r9 + 120]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 338241895
  mov ecx, dword ptr [r9 + 124]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 666307205
  mov ecx, dword ptr [r9 + 128]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 773529912
  mov ecx, dword ptr [r9 + 132]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1294757372
  mov ecx, dword ptr [r9 + 136]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1396182291
  mov ecx, dword ptr [r9 + 140]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1695183700
  mov ecx, dword ptr [r9 + 144]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1986661051
  mov ecx, dword ptr [r9 + 148]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2177026350
  mov ecx, dword ptr [r9 + 152]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2456956037
  mov ecx, dword ptr [r9 + 156]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2730485921
  mov ecx, dword ptr [r9 + 160]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2820302411
  mov ecx, dword ptr [r9 + 164]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3259730800
  mov ecx, dword ptr [r9 + 168]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3345764771
  mov ecx, dword ptr [r9 + 172]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3516065817
  mov ecx, dword ptr [r9 + 176]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3600352804
  mov ecx, dword ptr [r9 + 180]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 4094571909
  mov ecx, dword ptr [r9 + 184]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 275423344
  mov ecx, dword ptr [r9 + 188]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 430227734
  mov ecx, dword ptr [r9 + 192]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 506948616
  mov ecx, dword ptr [r9 + 196]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 659060556
  mov ecx, dword ptr [r9 + 200]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 883997877
  mov ecx, dword ptr [r9 + 204]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 958139571
  mov ecx, dword ptr [r9 + 208]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1322822218
  mov ecx, dword ptr [r9 + 212]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1537002063
  mov ecx, dword ptr [r9 + 216]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 1747873779
  mov ecx, dword ptr [r9 + 220]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 1955562222
  mov ecx, dword ptr [r9 + 224]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2024104815
  mov ecx, dword ptr [r9 + 228]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2227730452
  mov ecx, dword ptr [r9 + 232]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2361852424
  mov ecx, dword ptr [r9 + 236]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 2428436474
  mov ecx, dword ptr [r9 + 240]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 2756734187
  mov ecx, dword ptr [r9 + 244]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov eax, r11d
  mov dword ptr [rsp + 72], eax
  mov r8d, dword ptr [rsp + 44]
  mov dword ptr [rsp + 76], r8d
  mov ecx, dword ptr [rsp + 48]
  mov dword ptr [rsp + 80], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 56]
  mov dword ptr [rsp + 88], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 64]
  mov dword ptr [rsp + 96], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 60]
  mov dword ptr [rsp + 92], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 68]
  add r8d, edx
  add r8d, ecx
  add r8d, 3204031479
  mov ecx, dword ptr [r9 + 248]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 52]
  add eax, r8d
  mov dword ptr [rsp + 84], eax
  mov eax, r11d
  mov dword ptr [rsp + 44], eax
  mov r8d, dword ptr [rsp + 72]
  mov dword ptr [rsp + 48], r8d
  mov ecx, dword ptr [rsp + 76]
  mov dword ptr [rsp + 52], ecx
  mov edx, r8d
  and r8d, eax
  and edx, ecx
  and ecx, eax
  xor r8d, ecx
  xor r8d, edx
  mov ecx, eax
  mov edx, eax
  ror eax, 2
  ror ecx, 13
  xor eax, ecx
  ror edx, 22
  xor eax, edx
  add eax, r8d
  mov r8d, dword ptr [rsp + 84]
  mov dword ptr [rsp + 60], r8d
  mov edx, r8d
  not edx
  mov ecx, dword ptr [rsp + 92]
  mov dword ptr [rsp + 68], ecx
  and edx, ecx
  mov ecx, dword ptr [rsp + 88]
  mov dword ptr [rsp + 64], ecx
  and ecx, r8d
  xor ecx, edx
  mov edx, r8d
  mov r10d, r8d
  ror edx, 6
  ror r10d, 11
  xor edx, r10d
  ror r8d, 25
  xor edx, r8d
  mov r8d, dword ptr [rsp + 96]
  add r8d, edx
  add r8d, ecx
  add r8d, 3329325298
  mov ecx, dword ptr [r9 + 252]
  add r8d, ecx
  add eax, r8d
  mov r11d, eax
  mov eax, dword ptr [rsp + 80]
  add eax, r8d
  mov dword ptr [rsp + 56], eax
  mov rcx, qword ptr [rsp + 100]
  mov r8d, dword ptr [rcx + 0]
  add r8d, r11d
  mov dword ptr [rcx + 0], r8d
  mov r8d, dword ptr [rcx + 4]
  mov r11d, dword ptr [rsp + 44]
  add r8d, r11d
  mov dword ptr [rcx + 4], r8d
  mov r8d, dword ptr [rcx + 8]
  mov r11d, dword ptr [rsp + 48]
  add r8d, r11d
  mov dword ptr [rcx + 8], r8d
  mov r8d, dword ptr [rcx + 12]
  mov r11d, dword ptr [rsp + 52]
  add r8d, r11d
  mov dword ptr [rcx + 12], r8d
  mov r8d, dword ptr [rcx + 16]
  mov r11d, dword ptr [rsp + 56]
  add r8d, r11d
  mov dword ptr [rcx + 16], r8d
  mov r8d, dword ptr [rcx + 20]
  mov r11d, dword ptr [rsp + 60]
  add r8d, r11d
  mov dword ptr [rcx + 20], r8d
  mov r8d, dword ptr [rcx + 24]
  mov r11d, dword ptr [rsp + 64]
  add r8d, r11d
  mov dword ptr [rcx + 24], r8d
  mov r8d, dword ptr [rcx + 28]
  mov r11d, dword ptr [rsp + 68]
  add r8d, r11d
  mov dword ptr [rcx + 28], r8d
  mov dword ptr [rsp + 44], 0
  mov dword ptr [rsp + 48], 0
  mov dword ptr [rsp + 52], 0
  mov dword ptr [rsp + 56], 0
  mov dword ptr [rsp + 60], 0
  mov dword ptr [rsp + 64], 0
  mov dword ptr [rsp + 68], 0
  mov dword ptr [rsp + 72], 0
  mov dword ptr [rsp + 76], 0
  mov dword ptr [rsp + 80], 0
  mov dword ptr [rsp + 84], 0
  mov dword ptr [rsp + 88], 0
  mov dword ptr [rsp + 92], 0
  mov dword ptr [rsp + 96], 0
  mov dword ptr [rsp + 100], 0
  mov dword ptr [rsp + 104], 0
  mov dword ptr [rsp + 108], 0
  mov dword ptr [rsp + 112], 0
  mov dword ptr [rsp + 116], 0
  ret 
sha256_main_i_SHA256_Compute64Steps endp
ALIGN 16
sha256_main_i_SHA256_ComputeInitialWs proc
  mov r10, rcx
  add r10, rdx
  mov r9, r8
  mov eax, 0
  mov ecx, 0
  mov edx, 0
  mov r8d, 0
  mov r11d, 0
  mov eax, dword ptr [r10 + 0]
  bswap eax
  mov r8d, dword ptr [r10 + 4]
  bswap r8d
  mov ecx, dword ptr [r10 + 8]
  bswap ecx
  mov edx, dword ptr [r10 + 12]
  bswap edx
  mov r11d, dword ptr [r10 + 16]
  bswap r11d
  mov dword ptr [r9 + 0], eax
  mov dword ptr [r9 + 4], r8d
  mov dword ptr [r9 + 8], ecx
  mov dword ptr [r9 + 12], edx
  mov dword ptr [r9 + 16], r11d
  mov eax, dword ptr [r10 + 20]
  bswap eax
  mov r8d, dword ptr [r10 + 24]
  bswap r8d
  mov ecx, dword ptr [r10 + 28]
  bswap ecx
  mov edx, dword ptr [r10 + 32]
  bswap edx
  mov r11d, dword ptr [r10 + 36]
  bswap r11d
  mov dword ptr [r9 + 20], eax
  mov dword ptr [r9 + 24], r8d
  mov dword ptr [r9 + 28], ecx
  mov dword ptr [r9 + 32], edx
  mov dword ptr [r9 + 36], r11d
  mov eax, dword ptr [r10 + 40]
  bswap eax
  mov r8d, dword ptr [r10 + 44]
  bswap r8d
  mov ecx, dword ptr [r10 + 48]
  bswap ecx
  mov edx, dword ptr [r10 + 52]
  bswap edx
  mov r11d, dword ptr [r10 + 56]
  bswap r11d
  mov dword ptr [r9 + 40], eax
  mov dword ptr [r9 + 44], r8d
  mov dword ptr [r9 + 48], ecx
  mov dword ptr [r9 + 52], edx
  mov dword ptr [r9 + 56], r11d
  mov eax, dword ptr [r10 + 60]
  bswap eax
  mov dword ptr [r9 + 60], eax
  mov eax, dword ptr [r9 + 56]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 36]
  add edx, r8d
  mov eax, dword ptr [r9 + 4]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 0]
  add edx, eax
  mov dword ptr [r9 + 64], edx
  mov eax, dword ptr [r9 + 60]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 40]
  add edx, r8d
  mov eax, dword ptr [r9 + 8]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 4]
  add edx, eax
  mov dword ptr [r9 + 68], edx
  mov eax, dword ptr [r9 + 64]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 44]
  add edx, r8d
  mov eax, dword ptr [r9 + 12]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 8]
  add edx, eax
  mov dword ptr [r9 + 72], edx
  mov eax, dword ptr [r9 + 68]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 48]
  add edx, r8d
  mov eax, dword ptr [r9 + 16]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 12]
  add edx, eax
  mov dword ptr [r9 + 76], edx
  mov eax, dword ptr [r9 + 72]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 52]
  add edx, r8d
  mov eax, dword ptr [r9 + 20]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 16]
  add edx, eax
  mov dword ptr [r9 + 80], edx
  mov eax, dword ptr [r9 + 76]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 56]
  add edx, r8d
  mov eax, dword ptr [r9 + 24]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 20]
  add edx, eax
  mov dword ptr [r9 + 84], edx
  mov eax, dword ptr [r9 + 80]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 60]
  add edx, r8d
  mov eax, dword ptr [r9 + 28]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 24]
  add edx, eax
  mov dword ptr [r9 + 88], edx
  mov eax, dword ptr [r9 + 84]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 64]
  add edx, r8d
  mov eax, dword ptr [r9 + 32]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 28]
  add edx, eax
  mov dword ptr [r9 + 92], edx
  mov eax, dword ptr [r9 + 88]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 68]
  add edx, r8d
  mov eax, dword ptr [r9 + 36]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 32]
  add edx, eax
  mov dword ptr [r9 + 96], edx
  mov eax, dword ptr [r9 + 92]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 72]
  add edx, r8d
  mov eax, dword ptr [r9 + 40]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 36]
  add edx, eax
  mov dword ptr [r9 + 100], edx
  mov eax, dword ptr [r9 + 96]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 76]
  add edx, r8d
  mov eax, dword ptr [r9 + 44]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 40]
  add edx, eax
  mov dword ptr [r9 + 104], edx
  mov eax, dword ptr [r9 + 100]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 80]
  add edx, r8d
  mov eax, dword ptr [r9 + 48]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 44]
  add edx, eax
  mov dword ptr [r9 + 108], edx
  mov eax, dword ptr [r9 + 104]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 84]
  add edx, r8d
  mov eax, dword ptr [r9 + 52]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 48]
  add edx, eax
  mov dword ptr [r9 + 112], edx
  mov eax, dword ptr [r9 + 108]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 88]
  add edx, r8d
  mov eax, dword ptr [r9 + 56]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 52]
  add edx, eax
  mov dword ptr [r9 + 116], edx
  mov eax, dword ptr [r9 + 112]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 92]
  add edx, r8d
  mov eax, dword ptr [r9 + 60]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 56]
  add edx, eax
  mov dword ptr [r9 + 120], edx
  mov eax, dword ptr [r9 + 116]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 96]
  add edx, r8d
  mov eax, dword ptr [r9 + 64]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 60]
  add edx, eax
  mov dword ptr [r9 + 124], edx
  mov eax, dword ptr [r9 + 120]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 100]
  add edx, r8d
  mov eax, dword ptr [r9 + 68]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 64]
  add edx, eax
  mov dword ptr [r9 + 128], edx
  mov eax, dword ptr [r9 + 124]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 104]
  add edx, r8d
  mov eax, dword ptr [r9 + 72]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 68]
  add edx, eax
  mov dword ptr [r9 + 132], edx
  mov eax, dword ptr [r9 + 128]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 108]
  add edx, r8d
  mov eax, dword ptr [r9 + 76]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 72]
  add edx, eax
  mov dword ptr [r9 + 136], edx
  mov eax, dword ptr [r9 + 132]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 112]
  add edx, r8d
  mov eax, dword ptr [r9 + 80]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 76]
  add edx, eax
  mov dword ptr [r9 + 140], edx
  mov eax, dword ptr [r9 + 136]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 116]
  add edx, r8d
  mov eax, dword ptr [r9 + 84]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 80]
  add edx, eax
  mov dword ptr [r9 + 144], edx
  mov eax, dword ptr [r9 + 140]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 120]
  add edx, r8d
  mov eax, dword ptr [r9 + 88]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 84]
  add edx, eax
  mov dword ptr [r9 + 148], edx
  mov eax, dword ptr [r9 + 144]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 124]
  add edx, r8d
  mov eax, dword ptr [r9 + 92]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 88]
  add edx, eax
  mov dword ptr [r9 + 152], edx
  mov eax, dword ptr [r9 + 148]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 128]
  add edx, r8d
  mov eax, dword ptr [r9 + 96]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 92]
  add edx, eax
  mov dword ptr [r9 + 156], edx
  mov eax, dword ptr [r9 + 152]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 132]
  add edx, r8d
  mov eax, dword ptr [r9 + 100]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 96]
  add edx, eax
  mov dword ptr [r9 + 160], edx
  mov eax, dword ptr [r9 + 156]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 136]
  add edx, r8d
  mov eax, dword ptr [r9 + 104]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 100]
  add edx, eax
  mov dword ptr [r9 + 164], edx
  mov eax, dword ptr [r9 + 160]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 140]
  add edx, r8d
  mov eax, dword ptr [r9 + 108]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 104]
  add edx, eax
  mov dword ptr [r9 + 168], edx
  mov eax, dword ptr [r9 + 164]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 144]
  add edx, r8d
  mov eax, dword ptr [r9 + 112]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 108]
  add edx, eax
  mov dword ptr [r9 + 172], edx
  mov eax, dword ptr [r9 + 168]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 148]
  add edx, r8d
  mov eax, dword ptr [r9 + 116]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 112]
  add edx, eax
  mov dword ptr [r9 + 176], edx
  mov eax, dword ptr [r9 + 172]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 152]
  add edx, r8d
  mov eax, dword ptr [r9 + 120]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 116]
  add edx, eax
  mov dword ptr [r9 + 180], edx
  mov eax, dword ptr [r9 + 176]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 156]
  add edx, r8d
  mov eax, dword ptr [r9 + 124]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 120]
  add edx, eax
  mov dword ptr [r9 + 184], edx
  mov eax, dword ptr [r9 + 180]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 160]
  add edx, r8d
  mov eax, dword ptr [r9 + 128]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 124]
  add edx, eax
  mov dword ptr [r9 + 188], edx
  mov eax, dword ptr [r9 + 184]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 164]
  add edx, r8d
  mov eax, dword ptr [r9 + 132]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 128]
  add edx, eax
  mov dword ptr [r9 + 192], edx
  mov eax, dword ptr [r9 + 188]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 168]
  add edx, r8d
  mov eax, dword ptr [r9 + 136]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 132]
  add edx, eax
  mov dword ptr [r9 + 196], edx
  mov eax, dword ptr [r9 + 192]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 172]
  add edx, r8d
  mov eax, dword ptr [r9 + 140]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 136]
  add edx, eax
  mov dword ptr [r9 + 200], edx
  mov eax, dword ptr [r9 + 196]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 176]
  add edx, r8d
  mov eax, dword ptr [r9 + 144]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 140]
  add edx, eax
  mov dword ptr [r9 + 204], edx
  mov eax, dword ptr [r9 + 200]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 180]
  add edx, r8d
  mov eax, dword ptr [r9 + 148]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 144]
  add edx, eax
  mov dword ptr [r9 + 208], edx
  mov eax, dword ptr [r9 + 204]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 184]
  add edx, r8d
  mov eax, dword ptr [r9 + 152]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 148]
  add edx, eax
  mov dword ptr [r9 + 212], edx
  mov eax, dword ptr [r9 + 208]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 188]
  add edx, r8d
  mov eax, dword ptr [r9 + 156]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 152]
  add edx, eax
  mov dword ptr [r9 + 216], edx
  mov eax, dword ptr [r9 + 212]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 192]
  add edx, r8d
  mov eax, dword ptr [r9 + 160]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 156]
  add edx, eax
  mov dword ptr [r9 + 220], edx
  mov eax, dword ptr [r9 + 216]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 196]
  add edx, r8d
  mov eax, dword ptr [r9 + 164]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 160]
  add edx, eax
  mov dword ptr [r9 + 224], edx
  mov eax, dword ptr [r9 + 220]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 200]
  add edx, r8d
  mov eax, dword ptr [r9 + 168]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 164]
  add edx, eax
  mov dword ptr [r9 + 228], edx
  mov eax, dword ptr [r9 + 224]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 204]
  add edx, r8d
  mov eax, dword ptr [r9 + 172]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 168]
  add edx, eax
  mov dword ptr [r9 + 232], edx
  mov eax, dword ptr [r9 + 228]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 208]
  add edx, r8d
  mov eax, dword ptr [r9 + 176]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 172]
  add edx, eax
  mov dword ptr [r9 + 236], edx
  mov eax, dword ptr [r9 + 232]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 212]
  add edx, r8d
  mov eax, dword ptr [r9 + 180]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 176]
  add edx, eax
  mov dword ptr [r9 + 240], edx
  mov eax, dword ptr [r9 + 236]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 216]
  add edx, r8d
  mov eax, dword ptr [r9 + 184]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 180]
  add edx, eax
  mov dword ptr [r9 + 244], edx
  mov eax, dword ptr [r9 + 240]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 220]
  add edx, r8d
  mov eax, dword ptr [r9 + 188]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 184]
  add edx, eax
  mov dword ptr [r9 + 248], edx
  mov eax, dword ptr [r9 + 244]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 17
  ror ecx, 19
  xor r8d, ecx
  shr eax, 10
  xor r8d, eax
  mov edx, dword ptr [r9 + 224]
  add edx, r8d
  mov eax, dword ptr [r9 + 192]
  mov r8d, eax
  mov ecx, eax
  ror r8d, 7
  ror ecx, 18
  xor r8d, ecx
  shr eax, 3
  xor r8d, eax
  add edx, r8d
  mov eax, dword ptr [r9 + 188]
  add edx, eax
  mov dword ptr [r9 + 252], edx
  ret 
sha256_main_i_SHA256_ComputeInitialWs endp
end
