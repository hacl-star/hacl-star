# 20080118
# D. J. Bernstein
# Public domain.

int32 a

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

int32 x
int32 m
int32 out
stack32 bytes_backup
int32 bytes

stack32 eax_stack
stack32 ebx_stack
stack32 esi_stack
stack32 edi_stack
stack32 ebp_stack

int6464 diag0
int6464 diag1
int6464 diag2
int6464 diag3

int6464 a0
int6464 a1
int6464 a2
int6464 a3
int6464 a4
int6464 a5
int6464 a6
int6464 a7
int6464 b0
int6464 b1
int6464 b2
int6464 b3
int6464 b4
int6464 b5
int6464 b6
int6464 b7

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

  bytes_backup = bytes



diag0 = *(int128 *) (x + 0)
diag1 = *(int128 *) (x + 16)
diag2 = *(int128 *) (x + 32)
diag3 = *(int128 *) (x + 48)


i = 20

mainloop:

uint32323232	diag0 += diag1
		diag3 ^= diag0
		b3 = diag3
uint32323232	diag3 <<= 16
uint32323232	b3 >>= 16
		diag3 ^= b3

uint32323232			diag2 += diag3
				diag1 ^= diag2
				b1 = diag1
uint32323232			diag1 <<= 12
uint32323232			b1 >>= 20
				diag1 ^= b1

uint32323232					diag0 += diag1
						diag3 ^= diag0
						b3 = diag3
uint32323232					diag3 <<= 8
uint32323232					b3 >>= 24
		diag0 <<<= 32
						diag3 ^= b3

uint32323232							diag2 += diag3
		diag3 <<<= 64
								diag1 ^= diag2
		diag2 <<<= 96
								b1 = diag1
uint32323232							diag1 <<= 7
uint32323232							b1 >>= 25
								diag1 ^= b1

		 unsigned>? i -= 2

uint32323232	diag0 += diag1
		diag3 ^= diag0
		b3 = diag3
uint32323232	diag3 <<= 16
uint32323232	b3 >>= 16
		diag3 ^= b3

uint32323232			diag2 += diag3
				diag1 ^= diag2
				b1 = diag1
uint32323232			diag1 <<= 12
uint32323232			b1 >>= 20
				diag1 ^= b1

uint32323232					diag0 += diag1
						diag3 ^= diag0
						b3 = diag3
uint32323232					diag3 <<= 8
uint32323232					b3 >>= 24
		diag0 <<<= 96
						diag3 ^= b3

uint32323232							diag2 += diag3
		diag3 <<<= 64
								diag1 ^= diag2
		diag2 <<<= 32
								b1 = diag1
uint32323232							diag1 <<= 7
uint32323232							b1 >>= 25
								diag1 ^= b1


goto mainloop if unsigned>


uint32323232 diag0 += *(int128 *) (x + 0)
uint32323232 diag1 += *(int128 *) (x + 16)
uint32323232 diag2 += *(int128 *) (x + 32)
uint32323232 diag3 += *(int128 *) (x + 48)

uint32323232 diag0 ^= *(int128 *) (m + 0)
uint32323232 diag1 ^= *(int128 *) (m + 16)
uint32323232 diag2 ^= *(int128 *) (m + 32)
uint32323232 diag3 ^= *(int128 *) (m + 48)

*(int128 *) (out + 0) = diag0
*(int128 *) (out + 16) = diag1
*(int128 *) (out + 32) = diag2
*(int128 *) (out + 48) = diag3


  bytes = bytes_backup

  in12 = *(uint32 *) (x + 48)
  in13 = *(uint32 *) (x + 52)
  carry? in12 += 1
  in13 += 0 + carry
  *(uint32 *) (x + 48) = in12
  *(uint32 *) (x + 52) = in13

                         unsigned>? unsigned<? bytes - 64
  goto bytesatleast65 if unsigned>

    goto bytesatleast64 if !unsigned<
      m = out
      out = ctarget
      i = bytes
      while (i) { *out++ = *m++; --i }
    bytesatleast64:
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
