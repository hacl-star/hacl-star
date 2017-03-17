# 20080118
# D. J. Bernstein
# Public domain.

stack32 arg1
stack32 arg2
stack32 arg3
stack32 arg4
input arg1
input arg2
input arg3
input arg4

int32 eax
int32 ebx
int32 esi
int32 edi
int32 ebp
caller eax
caller ebx
caller esi
caller edi
caller ebp


int32 k
int32 kbits
int32 iv

int32 i

stack32 x_backup
int32 x
stack32 m_backup
int32 m
stack32 out_backup
int32 out
stack32 bytes_backup
int32 bytes

stack32 eax_stack
stack32 ebx_stack
stack32 esi_stack
stack32 edi_stack
stack32 ebp_stack

int32 a

int32 in0
int32 in1
int32 in2
int32 in3
int32 in4
int32 in5
int32 in6
int32 in7
int32 in8
int32 in9
int32 in10
int32 in11
int32 in12
int32 in13
int32 in14
int32 in15

int32 i0
int32 i1
int32 i2
int32 i3
int32 i4
int32 i5
int32 i6
int32 i7
int32 i8
int32 i9
int32 i10
int32 i11
int32 i12
int32 i13
int32 i14
int32 i15

stack32 x0
stack32 x1
stack32 x2
stack32 x3
stack32 x4
stack32 x5
stack32 x6
stack32 x7
stack32 x8
stack32 x9
stack32 x10
stack32 x11
stack32 x12
stack32 x13
stack32 x14
stack32 x15
stack32 j0
stack32 j1
stack32 j2
stack32 j3
stack32 j4
stack32 j5
stack32 j6
stack32 j7
stack32 j8
stack32 j9
stack32 j10
stack32 j11
stack32 j12
stack32 j13
stack32 j14
stack32 j15

stack512 tmp

stack32 ctarget


enter ECRYPT_keystream_bytes

eax_stack = eax
ebx_stack = ebx
esi_stack = esi
edi_stack = edi
ebp_stack = ebp

x = arg1
m = arg2
out = m
bytes = arg3

              unsigned>? bytes - 0
goto done if !unsigned>

a = 0
i = bytes
while (i) { *out++ = a; --i }
out -= bytes

goto start


enter ECRYPT_decrypt_bytes

eax_stack = eax
ebx_stack = ebx
esi_stack = esi
edi_stack = edi
ebp_stack = ebp

x = arg1
m = arg2
out = arg3
bytes = arg4

              unsigned>? bytes - 0
goto done if !unsigned>

goto start


enter ECRYPT_encrypt_bytes

eax_stack = eax
ebx_stack = ebx
esi_stack = esi
edi_stack = edi
ebp_stack = ebp

x = arg1
m = arg2
out = arg3
bytes = arg4

              unsigned>? bytes - 0
goto done if !unsigned>


start:

in0 = *(uint32 *) (x + 0)
in1 = *(uint32 *) (x + 4)
in2 = *(uint32 *) (x + 8)
j0 = in0
in3 = *(uint32 *) (x + 12)
j1 = in1
in4 = *(uint32 *) (x + 16)
j2 = in2
in5 = *(uint32 *) (x + 20)
j3 = in3
in6 = *(uint32 *) (x + 24)
j4 = in4
in7 = *(uint32 *) (x + 28)
j5 = in5
in8 = *(uint32 *) (x + 32)
j6 = in6
in9 = *(uint32 *) (x + 36)
j7 = in7
in10 = *(uint32 *) (x + 40)
j8 = in8
in11 = *(uint32 *) (x + 44)
j9 = in9
in12 = *(uint32 *) (x + 48)
j10 = in10
in13 = *(uint32 *) (x + 52)
j11 = in11
in14 = *(uint32 *) (x + 56)
j12 = in12
in15 = *(uint32 *) (x + 60)
j13 = in13
j14 = in14
j15 = in15

x_backup = x


bytesatleast1:

                  unsigned<? bytes - 64
  goto nocopy if !unsigned<

    ctarget = out

    out = &tmp
    i = bytes
    while (i) { *out++ = *m++; --i }
    out = &tmp
    m = &tmp

  nocopy:

  out_backup = out
  m_backup = m
  bytes_backup = bytes

  in0 = j0
  in1 = j1
  in2 = j2
  in3 = j3
  x0 = in0
  x1 = in1
  x2 = in2
  x3 = in3
  in4 = j4
  in5 = j5
  in6 = j6
  in7 = j7
  x4 = in4
  x5 = in5
  x6 = in6
  x7 = in7
  in8 = j8
  in9 = j9
  in10 = j10
  in11 = j11
  x8 = in8
  x9 = in9
  x10 = in10
  x11 = in11
  in12 = j12
  in13 = j13
  in14 = j14
  in15 = j15
  x12 = in12
  x13 = in13
  x14 = in14
  x15 = in15

  i = 20
  mainloop:


i0 = x0
i4 = x4
i0 += i4
i12 = x12
i12 ^= i0
i12 <<<= 16
i8 = x8
i8 += i12
i4 ^= i8
i4 <<<= 12
i0 += i4
x0 = i0
i12 ^= i0
		i1 = x1
		i5 = x5
		i1 += i5
		i13 = x13
		i13 ^= i1
		i13 <<<= 16
i12 <<<= 8
x12 = i12
i8 += i12
		i9 = x9
		i9 += i13
		i5 ^= i9
		i5 <<<= 12
		i1 += i5
		x1 = i1
		i13 ^= i1
x8 = i8
i4 ^= i8
i4 <<<= 7
x4 = i4
				i2 = x2
				i6 = x6
				i2 += i6
				i14 = x14
				i14 ^= i2
				i14 <<<= 16
		i13 <<<= 8
		x13 = i13
		i9 += i13
				i10 = x10
				i10 += i14
				i6 ^= i10
				i6 <<<= 12
				i2 += i6
				x2 = i2
				i14 ^= i2
		x9 = i9
		i5 ^= i9
		i5 <<<= 7
		x5 = i5
						i3 = x3
						i7 = x7
						i3 += i7
						i15 = x15
						i15 ^= i3
						i15 <<<= 16
				i14 <<<= 8
				x14 = i14
				i10 += i14
						i11 = x11
						i11 += i15
						i7 ^= i11
						i7 <<<= 12
						i3 += i7
						x3 = i3
						i15 ^= i3
						i15 <<<= 8
						i11 += i15
						x11 = i11
						i7 ^= i11
						i7 <<<= 7
						x7 = i7
				x10 = i10
				i6 ^= i10
				i6 <<<= 7
i0 = x0
i5 = x5
i0 += i5
i15 ^= i0
i15 <<<= 16
i10 = x10
i10 += i15
i5 ^= i10
i5 <<<= 12
i0 += i5
x0 = i0
i15 ^= i0
		i1 = x1
		i1 += i6
		i12 = x12
		i12 ^= i1
		i12 <<<= 16
i15 <<<= 8
x15 = i15
i10 += i15
		i11 = x11
		i11 += i12
		i6 ^= i11
		i6 <<<= 12
		i1 += i6
		x1 = i1
		i12 ^= i1
x10 = i10
i5 ^= i10
i5 <<<= 7
x5 = i5
				i2 = x2
				i7 = x7
				i2 += i7
				i13 = x13
				i13 ^= i2
				i13 <<<= 16
		i12 <<<= 8
		x12 = i12
		i11 += i12
				i8 = x8
				i8 += i13
				i7 ^= i8
				i7 <<<= 12
				i2 += i7
				x2 = i2
				i13 ^= i2
		x11 = i11
		i6 ^= i11
		i6 <<<= 7
		x6 = i6
						i3 = x3
						i4 = x4
						i3 += i4
						i14 = x14
						i14 ^= i3
						i14 <<<= 16
				i13 <<<= 8
				x13 = i13
				i8 += i13
						i9 = x9
						i9 += i14
						i4 ^= i9
						i4 <<<= 12
						i3 += i4
						x3 = i3
						i14 ^= i3
						i14 <<<= 8
						x14 = i14
						i9 += i14
				x8 = i8
				i7 ^= i8
				i7 <<<= 7
				x7 = i7
						x9 = i9
						i4 ^= i9
						i4 <<<= 7
						x4 = i4


                 unsigned>? i -= 2
goto mainloop if unsigned>



  out = out_backup
  m = m_backup

  in0 = x0
  in1 = x1
  in0 += j0
  in1 += j1
  in0 ^= *(uint32 *) (m + 0)
  in1 ^= *(uint32 *) (m + 4)
  *(uint32 *) (out + 0) = in0
  *(uint32 *) (out + 4) = in1
  in2 = x2
  in3 = x3
  in2 += j2
  in3 += j3
  in2 ^= *(uint32 *) (m + 8)
  in3 ^= *(uint32 *) (m + 12)
  *(uint32 *) (out + 8) = in2
  *(uint32 *) (out + 12) = in3
  in4 = x4
  in5 = x5
  in4 += j4
  in5 += j5
  in4 ^= *(uint32 *) (m + 16)
  in5 ^= *(uint32 *) (m + 20)
  *(uint32 *) (out + 16) = in4
  *(uint32 *) (out + 20) = in5
  in6 = x6
  in7 = x7
  in6 += j6
  in7 += j7
  in6 ^= *(uint32 *) (m + 24)
  in7 ^= *(uint32 *) (m + 28)
  *(uint32 *) (out + 24) = in6
  *(uint32 *) (out + 28) = in7
  in8 = x8
  in9 = x9
  in8 += j8
  in9 += j9
  in8 ^= *(uint32 *) (m + 32)
  in9 ^= *(uint32 *) (m + 36)
  *(uint32 *) (out + 32) = in8
  *(uint32 *) (out + 36) = in9
  in10 = x10
  in11 = x11
  in10 += j10
  in11 += j11
  in10 ^= *(uint32 *) (m + 40)
  in11 ^= *(uint32 *) (m + 44)
  *(uint32 *) (out + 40) = in10
  *(uint32 *) (out + 44) = in11
  in12 = x12
  in13 = x13
  in12 += j12
  in13 += j13
  in12 ^= *(uint32 *) (m + 48)
  in13 ^= *(uint32 *) (m + 52)
  *(uint32 *) (out + 48) = in12
  *(uint32 *) (out + 52) = in13
  in14 = x14
  in15 = x15
  in14 += j14
  in15 += j15
  in14 ^= *(uint32 *) (m + 56)
  in15 ^= *(uint32 *) (m + 60)
  *(uint32 *) (out + 56) = in14
  *(uint32 *) (out + 60) = in15

  bytes = bytes_backup

  in12 = j12
  in13 = j13
  carry? in12 += 1
  in13 += 0 + carry
  j12 = in12
  j13 = in13

                         unsigned>? unsigned<? bytes - 64
  goto bytesatleast65 if unsigned>

    goto bytesatleast64 if !unsigned<
      m = out
      out = ctarget
      i = bytes
      while (i) { *out++ = *m++; --i }
    bytesatleast64:

    x = x_backup
    in12 = j12
    in13 = j13
    *(uint32 *) (x + 48) = in12
    *(uint32 *) (x + 52) = in13

    done:

    eax = eax_stack
    ebx = ebx_stack
    esi = esi_stack
    edi = edi_stack
    ebp = ebp_stack

    leave

  bytesatleast65:

  bytes -= 64
  out += 64
  m += 64
goto bytesatleast1


enter ECRYPT_init
leave


enter ECRYPT_keysetup

  eax_stack = eax
  ebx_stack = ebx
  esi_stack = esi
  edi_stack = edi
  ebp_stack = ebp
  
  k = arg2
  kbits = arg3
  x = arg1

  in4 = *(uint32 *) (k + 0)
  in5 = *(uint32 *) (k + 4)
  in6 = *(uint32 *) (k + 8)
  in7 = *(uint32 *) (k + 12)
  *(uint32 *) (x + 16) = in4
  *(uint32 *) (x + 20) = in5
  *(uint32 *) (x + 24) = in6
  *(uint32 *) (x + 28) = in7

                   unsigned<? kbits - 256
  goto kbits128 if unsigned<

  kbits256:

    in8 = *(uint32 *) (k + 16)
    in9 = *(uint32 *) (k + 20)
    in10 = *(uint32 *) (k + 24)
    in11 = *(uint32 *) (k + 28)
    *(uint32 *) (x + 32) = in8
    *(uint32 *) (x + 36) = in9
    *(uint32 *) (x + 40) = in10
    *(uint32 *) (x + 44) = in11

    in0 = 1634760805
    in1 = 857760878
    in2 = 2036477234
    in3 = 1797285236
    *(uint32 *) (x + 0) = in0
    *(uint32 *) (x + 4) = in1
    *(uint32 *) (x + 8) = in2
    *(uint32 *) (x + 12) = in3

  goto keysetupdone

  kbits128:

    in8 = *(uint32 *) (k + 0)
    in9 = *(uint32 *) (k + 4)
    in10 = *(uint32 *) (k + 8)
    in11 = *(uint32 *) (k + 12)
    *(uint32 *) (x + 32) = in8
    *(uint32 *) (x + 36) = in9
    *(uint32 *) (x + 40) = in10
    *(uint32 *) (x + 44) = in11

    in0 = 1634760805
    in1 = 824206446
    in2 = 2036477238
    in3 = 1797285236
    *(uint32 *) (x + 0) = in0
    *(uint32 *) (x + 4) = in1
    *(uint32 *) (x + 8) = in2
    *(uint32 *) (x + 12) = in3

  keysetupdone:

  eax = eax_stack
  ebx = ebx_stack
  esi = esi_stack
  edi = edi_stack
  ebp = ebp_stack

leave


enter ECRYPT_ivsetup

  eax_stack = eax
  ebx_stack = ebx
  esi_stack = esi
  edi_stack = edi
  ebp_stack = ebp
  
  iv = arg2
  x = arg1

  in12 = 0
  in13 = 0
  in14 = *(uint32 *) (iv + 0)
  in15 = *(uint32 *) (iv + 4)
  *(uint32 *) (x + 48) = in12
  *(uint32 *) (x + 52) = in13
  *(uint32 *) (x + 56) = in14
  *(uint32 *) (x + 60) = in15

  eax = eax_stack
  ebx = ebx_stack
  esi = esi_stack
  edi = edi_stack
  ebp = ebp_stack

leave
