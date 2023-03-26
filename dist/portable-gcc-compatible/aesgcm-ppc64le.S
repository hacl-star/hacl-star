.text
.global aes128_key_expansion
aes128_key_expansion:

  lxvb16x 32+1, 0, 4
  stxvb16x 32+1, 0, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 1
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 16
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 2
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 32
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 4
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 48
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 8
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 64
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 16
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 80
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 32
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 96
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 64
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 112
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 128
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 128
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 27
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 144
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vspltisw 3, 8
  vsbox 2, 1
  lis 10, 54
  mtvsrws 32+4, 10
  vxor 2, 2, 4
  vrlw 2, 2, 3
  vspltw 2, 2, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vsldoi 3, 0, 1, 12
  vxor 1, 1, 3
  vxor 1, 1, 2
  li 10, 160
  stxvb16x 32+1, 10, 3
  vxor 1, 1, 1
  vxor 2, 2, 2
  vxor 3, 3, 3

  blr

.global aes128_keyhash_init
aes128_keyhash_init:

  vspltisw 0, 0
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  li 10, 32
  stxvb16x 32+0, 10, 3
  li 10, 32
  lxvb16x 32+1, 10, 3
  vmr 6, 1
  vmr 3, 1
  vspltisw 1, 0
  vspltisw 2, 1
  lis 10, -15872
  mtvsrws 32+4, 10
  lis 10, -32768
  mtvsrws 32+5, 10
  vsldoi 4, 4, 1, 8
  vsldoi 5, 5, 1, 12
  vsldoi 4, 4, 2, 4
  vmr 1, 3
  vspltisb 2, 1
  vsl 1, 1, 2
  vand 3, 3, 5
  vcmpequw 3, 3, 5
  vspltw 3, 3, 0
  vand 3, 3, 4
  vxor 1, 1, 3
  stxvb16x 32+1, 0, 3
  vmr 1, 6
  vmr 2, 6
  vspltisw 0, 0
  vsldoi 3, 1, 1, 8
  vsldoi 4, 0, 3, 8
  vsldoi 5, 3, 0, 8
  vpmsumd 3, 3, 2
  vpmsumd 4, 4, 2
  vpmsumd 5, 5, 2
  vsldoi 1, 3, 0, 8
  vsldoi 2, 0, 3, 8
  vxor 1, 1, 4
  vxor 2, 5, 2
  vspltisw 0, 0
  li 10, 31
  mtvsrws 32+3, 10
  vsrw 3, 1, 3
  vsldoi 3, 0, 3, 4
  vspltisb 0, 1
  vsl 1, 1, 0
  vsl 2, 2, 0
  vxor 2, 2, 3
  vmr 6, 2
  vxor 2, 2, 2
  lis 10, -7936
  mtvsrws 32+3, 10
  vsldoi 2, 3, 2, 12
  vspltisw 0, 0
  vsldoi 3, 1, 1, 8
  vsldoi 4, 0, 3, 8
  vsldoi 5, 3, 0, 8
  vpmsumd 3, 3, 2
  vpmsumd 4, 4, 2
  vpmsumd 5, 5, 2
  vsldoi 1, 3, 0, 8
  vsldoi 2, 0, 3, 8
  vxor 1, 1, 4
  vxor 2, 5, 2
  vspltisw 0, 0
  li 10, 31
  mtvsrws 32+3, 10
  vsrw 3, 1, 3
  vsldoi 3, 0, 3, 4
  vspltisb 0, 1
  vsl 1, 1, 0
  vsl 2, 2, 0
  vxor 2, 2, 3
  vmr 5, 2
  vxor 2, 2, 2
  lis 10, -7936
  mtvsrws 32+3, 10
  vsldoi 2, 3, 2, 12
  vpmsumd 1, 1, 2
  vspltisb 2, 1
  vsl 1, 1, 2
  vxor 1, 1, 5
  vxor 1, 1, 6
  vmr 3, 1
  vspltisw 1, 0
  vspltisw 2, 1
  lis 10, -15872
  mtvsrws 32+4, 10
  lis 10, -32768
  mtvsrws 32+5, 10
  vsldoi 4, 4, 1, 8
  vsldoi 5, 5, 1, 12
  vsldoi 4, 4, 2, 4
  vmr 1, 3
  vspltisb 2, 1
  vsl 1, 1, 2
  vand 3, 3, 5
  vcmpequw 3, 3, 5
  vspltw 3, 3, 0
  vand 3, 3, 4
  vxor 1, 1, 3
  li 10, 16
  stxvb16x 32+1, 10, 3

  blr

.global aes256_key_expansion
aes256_key_expansion:

  li 10, 16
  lxvb16x 32+1, 0, 4
  lxvb16x 32+3, 10, 4
  stxvb16x 32+1, 0, 3
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 1
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 32
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vsbox 2, 1
  vspltw 2, 2, 3
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vxor 3, 3, 2
  li 10, 48
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 2
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 64
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vsbox 2, 1
  vspltw 2, 2, 3
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vxor 3, 3, 2
  li 10, 80
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 4
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 96
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vsbox 2, 1
  vspltw 2, 2, 3
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vxor 3, 3, 2
  li 10, 112
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 8
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 128
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vsbox 2, 1
  vspltw 2, 2, 3
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vxor 3, 3, 2
  li 10, 144
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 16
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 160
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vsbox 2, 1
  vspltw 2, 2, 3
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vxor 3, 3, 2
  li 10, 176
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 32
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 192
  stxvb16x 32+1, 10, 3
  vspltisw 0, 0
  vsbox 2, 1
  vspltw 2, 2, 3
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vsldoi 4, 0, 3, 12
  vxor 3, 3, 4
  vxor 3, 3, 2
  li 10, 208
  stxvb16x 32+3, 10, 3
  vspltisw 0, 0
  vspltisw 4, 8
  vsbox 2, 3
  lis 10, 64
  mtvsrws 32+5, 10
  vxor 2, 2, 5
  vrlw 2, 2, 4
  vspltw 2, 2, 3
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vsldoi 4, 0, 1, 12
  vxor 1, 1, 4
  vxor 1, 1, 2
  li 10, 224
  stxvb16x 32+1, 10, 3
  vxor 1, 1, 1
  vxor 2, 2, 2
  vxor 3, 3, 3
  vxor 4, 4, 4

  blr

.global aes256_keyhash_init
aes256_keyhash_init:

  vspltisw 0, 0
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  li 10, 32
  stxvb16x 32+0, 10, 3
  li 10, 32
  lxvb16x 32+1, 10, 3
  vmr 6, 1
  vmr 3, 1
  vspltisw 1, 0
  vspltisw 2, 1
  lis 10, -15872
  mtvsrws 32+4, 10
  lis 10, -32768
  mtvsrws 32+5, 10
  vsldoi 4, 4, 1, 8
  vsldoi 5, 5, 1, 12
  vsldoi 4, 4, 2, 4
  vmr 1, 3
  vspltisb 2, 1
  vsl 1, 1, 2
  vand 3, 3, 5
  vcmpequw 3, 3, 5
  vspltw 3, 3, 0
  vand 3, 3, 4
  vxor 1, 1, 3
  stxvb16x 32+1, 0, 3
  vmr 1, 6
  vmr 2, 6
  vspltisw 0, 0
  vsldoi 3, 1, 1, 8
  vsldoi 4, 0, 3, 8
  vsldoi 5, 3, 0, 8
  vpmsumd 3, 3, 2
  vpmsumd 4, 4, 2
  vpmsumd 5, 5, 2
  vsldoi 1, 3, 0, 8
  vsldoi 2, 0, 3, 8
  vxor 1, 1, 4
  vxor 2, 5, 2
  vspltisw 0, 0
  li 10, 31
  mtvsrws 32+3, 10
  vsrw 3, 1, 3
  vsldoi 3, 0, 3, 4
  vspltisb 0, 1
  vsl 1, 1, 0
  vsl 2, 2, 0
  vxor 2, 2, 3
  vmr 6, 2
  vxor 2, 2, 2
  lis 10, -7936
  mtvsrws 32+3, 10
  vsldoi 2, 3, 2, 12
  vspltisw 0, 0
  vsldoi 3, 1, 1, 8
  vsldoi 4, 0, 3, 8
  vsldoi 5, 3, 0, 8
  vpmsumd 3, 3, 2
  vpmsumd 4, 4, 2
  vpmsumd 5, 5, 2
  vsldoi 1, 3, 0, 8
  vsldoi 2, 0, 3, 8
  vxor 1, 1, 4
  vxor 2, 5, 2
  vspltisw 0, 0
  li 10, 31
  mtvsrws 32+3, 10
  vsrw 3, 1, 3
  vsldoi 3, 0, 3, 4
  vspltisb 0, 1
  vsl 1, 1, 0
  vsl 2, 2, 0
  vxor 2, 2, 3
  vmr 5, 2
  vxor 2, 2, 2
  lis 10, -7936
  mtvsrws 32+3, 10
  vsldoi 2, 3, 2, 12
  vpmsumd 1, 1, 2
  vspltisb 2, 1
  vsl 1, 1, 2
  vxor 1, 1, 5
  vxor 1, 1, 6
  vmr 3, 1
  vspltisw 1, 0
  vspltisw 2, 1
  lis 10, -15872
  mtvsrws 32+4, 10
  lis 10, -32768
  mtvsrws 32+5, 10
  vsldoi 4, 4, 1, 8
  vsldoi 5, 5, 1, 12
  vsldoi 4, 4, 2, 4
  vmr 1, 3
  vspltisb 2, 1
  vsl 1, 1, 2
  vand 3, 3, 5
  vcmpequw 3, 3, 5
  vspltw 3, 3, 0
  vand 3, 3, 4
  vxor 1, 1, 3
  li 10, 16
  stxvb16x 32+1, 10, 3

  blr

.global compute_iv_stdcall
compute_iv_stdcall:

  mr 9, 8
  cmpldi 9, 12
  bne L0
  lxvb16x 32+0, 0, 4
  vspltisw 1, 1
  vsldoi 0, 0, 0, 12
  vsldoi 0, 0, 1, 4
  stxvb16x 32+0, 0, 3
  b L1
L0:
  sldi 8, 6, 4
  vspltisw 1, 0
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L3
.align 4
L2:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L3:
  cmpldi 6, 2
  bge L2
  cmpldi 6, 0
  ble L4
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L5
L4:
L5:
  cmpld 9, 8
  ble L6
  lxvb16x 32+9, 0, 4
  li 10, 15
  and 8, 9, 10
  cmpldi 8, 8
  bge L8
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L9
L8:
  cmpldi 8, 8
  bne L10
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L11
L10:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L11:
L9:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L7
L6:
L7:
  mr 6, 9
  li 7, 0
  sldi 6, 6, 3
  sldi 7, 7, 3
  mtvsrdd 32+9, 6, 7
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  stxvb16x 32+1, 0, 3
L1:

  blr

.global gcm128_encrypt
gcm128_encrypt:

  subi 1, 1, 96
  std 25, 0(1)
  std 26, 8(1)
  std 27, 16(1)
  std 28, 24(1)
  std 29, 32(1)
  std 30, 40(1)
  std 31, 48(1)
  stxv 32+20, 64(1)
  stxv 32+21, 80(1)
  mr 25, 3
  ld 5, 88(25)
  ld 4, 0(25)
  ld 7, 48(25)
  ld 6, 56(25)
  ld 9, 64(25)
  sldi 8, 6, 4
  vspltisw 1, 0
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L13
.align 4
L12:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L13:
  cmpldi 6, 2
  bge L12
  cmpldi 6, 0
  ble L14
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L15
L14:
L15:
  cmpld 9, 8
  ble L16
  lxvb16x 32+9, 0, 4
  li 10, 15
  and 8, 9, 10
  cmpldi 8, 8
  bge L18
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L19
L18:
  cmpldi 8, 8
  bne L20
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L21
L20:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L21:
L19:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L17
L16:
L17:
  ld 10, 72(25)
  lxvb16x 32+7, 0, 10
  vmr 21, 7
  vspltisw 10, 1
  vspltisw 4, 0
  vsldoi 10, 4, 10, 4
  vadduwm 7, 7, 10
  ld 3, 8(25)
  ld 7, 16(25)
  ld 6, 24(25)
  ld 4, 80(25)
  vmr 20, 1
  lis 26, 21845
  addi 26, 26, 21845
  sldi 10, 26, 32
  add 26, 26, 10
  li 10, -1
  sub 26, 10, 26
  addi 26, 26, 1
  mulhdu 10, 6, 26
  srdi 10, 10, 2
  add 26, 10, 10
  add 26, 26, 10
  add 26, 26, 26
  sub 26, 6, 26
  sub 6, 6, 26
  vspltisw 8, 1
  vspltisw 9, 2
  vspltisw 10, 3
  vspltisw 11, 4
  vspltisw 12, 5
  vspltisw 13, 6
  vspltisw 14, 0
  vsldoi 8, 14, 8, 4
  vsldoi 9, 14, 9, 4
  vsldoi 10, 14, 10, 4
  vsldoi 11, 14, 11, 4
  vsldoi 12, 14, 12, 4
  vsldoi 13, 14, 13, 4
  li 27, 16
  li 28, 32
  li 29, 48
  li 30, 64
  li 31, 80
  li 8, 0
  b L23
.align 4
L22:
  vmr 0, 7
  vadduwm 1, 7, 8
  vadduwm 2, 7, 9
  vadduwm 3, 7, 10
  vadduwm 4, 7, 11
  vadduwm 5, 7, 12
  li 10, 0
  lxvb16x 32+6, 10, 4
  vxor 0, 0, 6
  vxor 1, 1, 6
  vxor 2, 2, 6
  vxor 3, 3, 6
  vxor 4, 4, 6
  vxor 5, 5, 6
  li 10, 16
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 32
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 48
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 64
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 80
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 96
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 112
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 128
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 144
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 160
  lxvb16x 32+6, 10, 4
  vcipherlast 0, 0, 6
  vcipherlast 1, 1, 6
  vcipherlast 2, 2, 6
  vcipherlast 3, 3, 6
  vcipherlast 4, 4, 6
  vcipherlast 5, 5, 6
  vxor 6, 6, 6
  lxvb16x 32+14, 0, 3
  lxvb16x 32+15, 27, 3
  lxvb16x 32+16, 28, 3
  lxvb16x 32+17, 29, 3
  lxvb16x 32+18, 30, 3
  lxvb16x 32+19, 31, 3
  vxor 0, 14, 0
  vxor 1, 15, 1
  vxor 2, 16, 2
  vxor 3, 17, 3
  vxor 4, 18, 4
  vxor 5, 19, 5
  stxvb16x 32+0, 0, 7
  stxvb16x 32+1, 27, 7
  stxvb16x 32+2, 28, 7
  stxvb16x 32+3, 29, 7
  stxvb16x 32+4, 30, 7
  stxvb16x 32+5, 31, 7
  addi 8, 8, 6
  addi 3, 3, 96
  addi 7, 7, 96
  vadduwm 7, 7, 13
.align 4
L23:
  cmpld 8, 6
  bne L22
  vspltisw 3, 1
  vspltisw 4, 0
  vsldoi 3, 4, 3, 4
  li 8, 0
  li 9, 0
  b L25
.align 4
L24:
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  lxvb16x 32+2, 9, 3
  vxor 2, 2, 0
  stxvb16x 32+2, 9, 7
  addi 8, 8, 1
  addi 9, 9, 16
  vadduwm 7, 7, 3
.align 4
L25:
  cmpld 8, 26
  bne L24
  sldi 10, 6, 4
  sub 3, 3, 10
  sub 7, 7, 10
  add 6, 6, 26
  vmr 15, 7
  vmr 1, 20
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L27
.align 4
L26:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L27:
  cmpldi 6, 2
  bge L26
  cmpldi 6, 0
  ble L28
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L29
L28:
L29:
  vmr 7, 15
  ld 7, 24(25)
  sldi 7, 7, 4
  ld 6, 40(25)
  cmpld 6, 7
  ble L30
  ld 3, 32(25)
  li 10, 15
  and 8, 6, 10
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  lxvb16x 32+9, 0, 3
  vxor 9, 9, 0
  stxvb16x 32+9, 0, 3
  cmpldi 8, 8
  bge L32
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L33
L32:
  cmpldi 8, 8
  bne L34
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L35
L34:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L35:
L33:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L31
L30:
L31:
  ld 7, 64(25)
  sldi 6, 6, 3
  sldi 7, 7, 3
  mtvsrdd 32+9, 6, 7
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  vmr 7, 21
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  vxor 1, 1, 0
  ld 3, 96(25)
  stxvb16x 32+1, 0, 3
  ld 25, 0(1)
  ld 26, 8(1)
  ld 27, 16(1)
  ld 28, 24(1)
  ld 29, 32(1)
  ld 30, 40(1)
  ld 31, 48(1)
  lxv 32+20, 64(1)
  lxv 32+21, 80(1)
  addi 1, 1, 96

  blr

.global gcm256_encrypt
gcm256_encrypt:

  subi 1, 1, 96
  std 25, 0(1)
  std 26, 8(1)
  std 27, 16(1)
  std 28, 24(1)
  std 29, 32(1)
  std 30, 40(1)
  std 31, 48(1)
  stxv 32+20, 64(1)
  stxv 32+21, 80(1)
  mr 25, 3
  ld 5, 88(25)
  ld 4, 0(25)
  ld 7, 48(25)
  ld 6, 56(25)
  ld 9, 64(25)
  sldi 8, 6, 4
  vspltisw 1, 0
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L37
.align 4
L36:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L37:
  cmpldi 6, 2
  bge L36
  cmpldi 6, 0
  ble L38
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L39
L38:
L39:
  cmpld 9, 8
  ble L40
  lxvb16x 32+9, 0, 4
  li 10, 15
  and 8, 9, 10
  cmpldi 8, 8
  bge L42
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L43
L42:
  cmpldi 8, 8
  bne L44
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L45
L44:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L45:
L43:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L41
L40:
L41:
  ld 10, 72(25)
  lxvb16x 32+7, 0, 10
  vmr 21, 7
  vspltisw 10, 1
  vspltisw 4, 0
  vsldoi 10, 4, 10, 4
  vadduwm 7, 7, 10
  ld 3, 8(25)
  ld 7, 16(25)
  ld 6, 24(25)
  ld 4, 80(25)
  vmr 20, 1
  lis 26, 21845
  addi 26, 26, 21845
  sldi 10, 26, 32
  add 26, 26, 10
  li 10, -1
  sub 26, 10, 26
  addi 26, 26, 1
  mulhdu 10, 6, 26
  srdi 10, 10, 2
  add 26, 10, 10
  add 26, 26, 10
  add 26, 26, 26
  sub 26, 6, 26
  sub 6, 6, 26
  vspltisw 8, 1
  vspltisw 9, 2
  vspltisw 10, 3
  vspltisw 11, 4
  vspltisw 12, 5
  vspltisw 13, 6
  vspltisw 14, 0
  vsldoi 8, 14, 8, 4
  vsldoi 9, 14, 9, 4
  vsldoi 10, 14, 10, 4
  vsldoi 11, 14, 11, 4
  vsldoi 12, 14, 12, 4
  vsldoi 13, 14, 13, 4
  li 27, 16
  li 28, 32
  li 29, 48
  li 30, 64
  li 31, 80
  li 8, 0
  b L47
.align 4
L46:
  vmr 0, 7
  vadduwm 1, 7, 8
  vadduwm 2, 7, 9
  vadduwm 3, 7, 10
  vadduwm 4, 7, 11
  vadduwm 5, 7, 12
  li 10, 0
  lxvb16x 32+6, 10, 4
  vxor 0, 0, 6
  vxor 1, 1, 6
  vxor 2, 2, 6
  vxor 3, 3, 6
  vxor 4, 4, 6
  vxor 5, 5, 6
  li 10, 16
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 32
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 48
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 64
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 80
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 96
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 112
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 128
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 144
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 160
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 176
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 192
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 208
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 224
  lxvb16x 32+6, 10, 4
  vcipherlast 0, 0, 6
  vcipherlast 1, 1, 6
  vcipherlast 2, 2, 6
  vcipherlast 3, 3, 6
  vcipherlast 4, 4, 6
  vcipherlast 5, 5, 6
  vxor 6, 6, 6
  lxvb16x 32+14, 0, 3
  lxvb16x 32+15, 27, 3
  lxvb16x 32+16, 28, 3
  lxvb16x 32+17, 29, 3
  lxvb16x 32+18, 30, 3
  lxvb16x 32+19, 31, 3
  vxor 0, 14, 0
  vxor 1, 15, 1
  vxor 2, 16, 2
  vxor 3, 17, 3
  vxor 4, 18, 4
  vxor 5, 19, 5
  stxvb16x 32+0, 0, 7
  stxvb16x 32+1, 27, 7
  stxvb16x 32+2, 28, 7
  stxvb16x 32+3, 29, 7
  stxvb16x 32+4, 30, 7
  stxvb16x 32+5, 31, 7
  addi 8, 8, 6
  addi 3, 3, 96
  addi 7, 7, 96
  vadduwm 7, 7, 13
.align 4
L47:
  cmpld 8, 6
  bne L46
  vspltisw 3, 1
  vspltisw 4, 0
  vsldoi 3, 4, 3, 4
  li 8, 0
  li 9, 0
  b L49
.align 4
L48:
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  lxvb16x 32+2, 9, 3
  vxor 2, 2, 0
  stxvb16x 32+2, 9, 7
  addi 8, 8, 1
  addi 9, 9, 16
  vadduwm 7, 7, 3
.align 4
L49:
  cmpld 8, 26
  bne L48
  sldi 10, 6, 4
  sub 3, 3, 10
  sub 7, 7, 10
  add 6, 6, 26
  vmr 15, 7
  vmr 1, 20
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L51
.align 4
L50:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L51:
  cmpldi 6, 2
  bge L50
  cmpldi 6, 0
  ble L52
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L53
L52:
L53:
  vmr 7, 15
  ld 7, 24(25)
  sldi 7, 7, 4
  ld 6, 40(25)
  cmpld 6, 7
  ble L54
  ld 3, 32(25)
  li 10, 15
  and 8, 6, 10
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  lxvb16x 32+9, 0, 3
  vxor 9, 9, 0
  stxvb16x 32+9, 0, 3
  cmpldi 8, 8
  bge L56
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L57
L56:
  cmpldi 8, 8
  bne L58
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L59
L58:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L59:
L57:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L55
L54:
L55:
  ld 7, 64(25)
  sldi 6, 6, 3
  sldi 7, 7, 3
  mtvsrdd 32+9, 6, 7
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  vmr 7, 21
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  vxor 1, 1, 0
  ld 3, 96(25)
  stxvb16x 32+1, 0, 3
  ld 25, 0(1)
  ld 26, 8(1)
  ld 27, 16(1)
  ld 28, 24(1)
  ld 29, 32(1)
  ld 30, 40(1)
  ld 31, 48(1)
  lxv 32+20, 64(1)
  lxv 32+21, 80(1)
  addi 1, 1, 96

  blr

.global gcm128_decrypt
gcm128_decrypt:

  subi 1, 1, 96
  std 25, 0(1)
  std 26, 8(1)
  std 27, 16(1)
  std 28, 24(1)
  std 29, 32(1)
  std 30, 40(1)
  std 31, 48(1)
  stxv 32+20, 64(1)
  stxv 32+21, 80(1)
  mr 25, 3
  ld 5, 88(25)
  ld 4, 0(25)
  ld 7, 48(25)
  ld 6, 56(25)
  ld 9, 64(25)
  sldi 8, 6, 4
  vspltisw 1, 0
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L61
.align 4
L60:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L61:
  cmpldi 6, 2
  bge L60
  cmpldi 6, 0
  ble L62
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L63
L62:
L63:
  cmpld 9, 8
  ble L64
  lxvb16x 32+9, 0, 4
  li 10, 15
  and 8, 9, 10
  cmpldi 8, 8
  bge L66
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L67
L66:
  cmpldi 8, 8
  bne L68
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L69
L68:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L69:
L67:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L65
L64:
L65:
  ld 10, 72(25)
  lxvb16x 32+7, 0, 10
  vmr 21, 7
  vspltisw 10, 1
  vspltisw 4, 0
  vsldoi 10, 4, 10, 4
  vadduwm 7, 7, 10
  ld 3, 8(25)
  ld 7, 16(25)
  ld 6, 24(25)
  ld 4, 80(25)
  vmr 15, 7
  mr 8, 7
  mr 9, 6
  mr 7, 3
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L71
.align 4
L70:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L71:
  cmpldi 6, 2
  bge L70
  cmpldi 6, 0
  ble L72
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L73
L72:
L73:
  vmr 20, 1
  vmr 7, 15
  mr 7, 8
  mr 6, 9
  lis 26, 21845
  addi 26, 26, 21845
  sldi 10, 26, 32
  add 26, 26, 10
  li 10, -1
  sub 26, 10, 26
  addi 26, 26, 1
  mulhdu 10, 6, 26
  srdi 10, 10, 2
  add 26, 10, 10
  add 26, 26, 10
  add 26, 26, 26
  sub 26, 6, 26
  sub 6, 6, 26
  vspltisw 8, 1
  vspltisw 9, 2
  vspltisw 10, 3
  vspltisw 11, 4
  vspltisw 12, 5
  vspltisw 13, 6
  vspltisw 14, 0
  vsldoi 8, 14, 8, 4
  vsldoi 9, 14, 9, 4
  vsldoi 10, 14, 10, 4
  vsldoi 11, 14, 11, 4
  vsldoi 12, 14, 12, 4
  vsldoi 13, 14, 13, 4
  li 27, 16
  li 28, 32
  li 29, 48
  li 30, 64
  li 31, 80
  li 8, 0
  b L75
.align 4
L74:
  vmr 0, 7
  vadduwm 1, 7, 8
  vadduwm 2, 7, 9
  vadduwm 3, 7, 10
  vadduwm 4, 7, 11
  vadduwm 5, 7, 12
  li 10, 0
  lxvb16x 32+6, 10, 4
  vxor 0, 0, 6
  vxor 1, 1, 6
  vxor 2, 2, 6
  vxor 3, 3, 6
  vxor 4, 4, 6
  vxor 5, 5, 6
  li 10, 16
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 32
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 48
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 64
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 80
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 96
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 112
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 128
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 144
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 160
  lxvb16x 32+6, 10, 4
  vcipherlast 0, 0, 6
  vcipherlast 1, 1, 6
  vcipherlast 2, 2, 6
  vcipherlast 3, 3, 6
  vcipherlast 4, 4, 6
  vcipherlast 5, 5, 6
  vxor 6, 6, 6
  lxvb16x 32+14, 0, 3
  lxvb16x 32+15, 27, 3
  lxvb16x 32+16, 28, 3
  lxvb16x 32+17, 29, 3
  lxvb16x 32+18, 30, 3
  lxvb16x 32+19, 31, 3
  vxor 0, 14, 0
  vxor 1, 15, 1
  vxor 2, 16, 2
  vxor 3, 17, 3
  vxor 4, 18, 4
  vxor 5, 19, 5
  stxvb16x 32+0, 0, 7
  stxvb16x 32+1, 27, 7
  stxvb16x 32+2, 28, 7
  stxvb16x 32+3, 29, 7
  stxvb16x 32+4, 30, 7
  stxvb16x 32+5, 31, 7
  addi 8, 8, 6
  addi 3, 3, 96
  addi 7, 7, 96
  vadduwm 7, 7, 13
.align 4
L75:
  cmpld 8, 6
  bne L74
  vspltisw 3, 1
  vspltisw 4, 0
  vsldoi 3, 4, 3, 4
  li 8, 0
  li 9, 0
  b L77
.align 4
L76:
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  lxvb16x 32+2, 9, 3
  vxor 2, 2, 0
  stxvb16x 32+2, 9, 7
  addi 8, 8, 1
  addi 9, 9, 16
  vadduwm 7, 7, 3
.align 4
L77:
  cmpld 8, 26
  bne L76
  sldi 10, 6, 4
  sub 3, 3, 10
  sub 7, 7, 10
  add 6, 6, 26
  vmr 1, 20
  ld 7, 24(25)
  sldi 7, 7, 4
  ld 6, 40(25)
  cmpld 6, 7
  ble L78
  ld 3, 32(25)
  li 10, 15
  and 8, 6, 10
  vmr 11, 7
  lxvb16x 32+9, 0, 3
  vmr 12, 9
  cmpldi 8, 8
  bge L80
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L81
L80:
  cmpldi 8, 8
  bne L82
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L83
L82:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L83:
L81:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  vmr 0, 11
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  vxor 12, 12, 0
  stxvb16x 32+12, 0, 3
  b L79
L78:
L79:
  ld 7, 64(25)
  sldi 6, 6, 3
  sldi 7, 7, 3
  mtvsrdd 32+9, 6, 7
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  vmr 7, 21
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  vxor 1, 1, 0
  ld 3, 96(25)
  lxvb16x 32+0, 0, 3
  vcmpequw 0, 0, 1
  mfvsrld 4, 32+0
  li 5, 1
  addc 3, 4, 5
  li 3, 0
  adde 3, 3, 3
  xor 3, 5, 3
  mr 6, 3
  mfvsrd 4, 32+0
  li 5, 1
  addc 3, 4, 5
  li 3, 0
  adde 3, 3, 3
  xor 3, 5, 3
  add 3, 6, 3
  ld 25, 0(1)
  ld 26, 8(1)
  ld 27, 16(1)
  ld 28, 24(1)
  ld 29, 32(1)
  ld 30, 40(1)
  ld 31, 48(1)
  lxv 32+20, 64(1)
  lxv 32+21, 80(1)
  addi 1, 1, 96

  blr

.global gcm256_decrypt
gcm256_decrypt:

  subi 1, 1, 96
  std 25, 0(1)
  std 26, 8(1)
  std 27, 16(1)
  std 28, 24(1)
  std 29, 32(1)
  std 30, 40(1)
  std 31, 48(1)
  stxv 32+20, 64(1)
  stxv 32+21, 80(1)
  mr 25, 3
  ld 5, 88(25)
  ld 4, 0(25)
  ld 7, 48(25)
  ld 6, 56(25)
  ld 9, 64(25)
  sldi 8, 6, 4
  vspltisw 1, 0
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L85
.align 4
L84:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L85:
  cmpldi 6, 2
  bge L84
  cmpldi 6, 0
  ble L86
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L87
L86:
L87:
  cmpld 9, 8
  ble L88
  lxvb16x 32+9, 0, 4
  li 10, 15
  and 8, 9, 10
  cmpldi 8, 8
  bge L90
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L91
L90:
  cmpldi 8, 8
  bne L92
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L93
L92:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L93:
L91:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L89
L88:
L89:
  ld 10, 72(25)
  lxvb16x 32+7, 0, 10
  vmr 21, 7
  vspltisw 10, 1
  vspltisw 4, 0
  vsldoi 10, 4, 10, 4
  vadduwm 7, 7, 10
  ld 3, 8(25)
  ld 7, 16(25)
  ld 6, 24(25)
  ld 4, 80(25)
  vmr 15, 7
  mr 8, 7
  mr 9, 6
  mr 7, 3
  li 10, 16
  lxvb16x 32+5, 0, 5
  lxvb16x 32+12, 10, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vsldoi 12, 12, 12, 8
  vsldoi 14, 0, 12, 8
  vsldoi 13, 12, 0, 8
  b L95
.align 4
L94:
  li 10, 16
  lxvb16x 32+0, 0, 7
  lxvb16x 32+8, 10, 7
  vpmsumd 2, 8, 7
  vpmsumd 3, 8, 5
  vpmsumd 4, 8, 6
  vxor 0, 1, 0
  vpmsumd 9, 0, 14
  vpmsumd 10, 0, 12
  vpmsumd 11, 0, 13
  vxor 2, 2, 9
  vxor 3, 3, 10
  vxor 4, 4, 11
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  addi 7, 7, 32
  subi 6, 6, 2
.align 4
L95:
  cmpldi 6, 2
  bge L94
  cmpldi 6, 0
  ble L96
  lxvb16x 32+0, 0, 7
  vxor 0, 1, 0
  vpmsumd 2, 0, 7
  vpmsumd 3, 0, 5
  vpmsumd 4, 0, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  b L97
L96:
L97:
  vmr 20, 1
  vmr 7, 15
  mr 7, 8
  mr 6, 9
  lis 26, 21845
  addi 26, 26, 21845
  sldi 10, 26, 32
  add 26, 26, 10
  li 10, -1
  sub 26, 10, 26
  addi 26, 26, 1
  mulhdu 10, 6, 26
  srdi 10, 10, 2
  add 26, 10, 10
  add 26, 26, 10
  add 26, 26, 26
  sub 26, 6, 26
  sub 6, 6, 26
  vspltisw 8, 1
  vspltisw 9, 2
  vspltisw 10, 3
  vspltisw 11, 4
  vspltisw 12, 5
  vspltisw 13, 6
  vspltisw 14, 0
  vsldoi 8, 14, 8, 4
  vsldoi 9, 14, 9, 4
  vsldoi 10, 14, 10, 4
  vsldoi 11, 14, 11, 4
  vsldoi 12, 14, 12, 4
  vsldoi 13, 14, 13, 4
  li 27, 16
  li 28, 32
  li 29, 48
  li 30, 64
  li 31, 80
  li 8, 0
  b L99
.align 4
L98:
  vmr 0, 7
  vadduwm 1, 7, 8
  vadduwm 2, 7, 9
  vadduwm 3, 7, 10
  vadduwm 4, 7, 11
  vadduwm 5, 7, 12
  li 10, 0
  lxvb16x 32+6, 10, 4
  vxor 0, 0, 6
  vxor 1, 1, 6
  vxor 2, 2, 6
  vxor 3, 3, 6
  vxor 4, 4, 6
  vxor 5, 5, 6
  li 10, 16
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 32
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 48
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 64
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 80
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 96
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 112
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 128
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 144
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 160
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 176
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 192
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 208
  lxvb16x 32+6, 10, 4
  vcipher 0, 0, 6
  vcipher 1, 1, 6
  vcipher 2, 2, 6
  vcipher 3, 3, 6
  vcipher 4, 4, 6
  vcipher 5, 5, 6
  li 10, 224
  lxvb16x 32+6, 10, 4
  vcipherlast 0, 0, 6
  vcipherlast 1, 1, 6
  vcipherlast 2, 2, 6
  vcipherlast 3, 3, 6
  vcipherlast 4, 4, 6
  vcipherlast 5, 5, 6
  vxor 6, 6, 6
  lxvb16x 32+14, 0, 3
  lxvb16x 32+15, 27, 3
  lxvb16x 32+16, 28, 3
  lxvb16x 32+17, 29, 3
  lxvb16x 32+18, 30, 3
  lxvb16x 32+19, 31, 3
  vxor 0, 14, 0
  vxor 1, 15, 1
  vxor 2, 16, 2
  vxor 3, 17, 3
  vxor 4, 18, 4
  vxor 5, 19, 5
  stxvb16x 32+0, 0, 7
  stxvb16x 32+1, 27, 7
  stxvb16x 32+2, 28, 7
  stxvb16x 32+3, 29, 7
  stxvb16x 32+4, 30, 7
  stxvb16x 32+5, 31, 7
  addi 8, 8, 6
  addi 3, 3, 96
  addi 7, 7, 96
  vadduwm 7, 7, 13
.align 4
L99:
  cmpld 8, 6
  bne L98
  vspltisw 3, 1
  vspltisw 4, 0
  vsldoi 3, 4, 3, 4
  li 8, 0
  li 9, 0
  b L101
.align 4
L100:
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  lxvb16x 32+2, 9, 3
  vxor 2, 2, 0
  stxvb16x 32+2, 9, 7
  addi 8, 8, 1
  addi 9, 9, 16
  vadduwm 7, 7, 3
.align 4
L101:
  cmpld 8, 26
  bne L100
  sldi 10, 6, 4
  sub 3, 3, 10
  sub 7, 7, 10
  add 6, 6, 26
  vmr 1, 20
  ld 7, 24(25)
  sldi 7, 7, 4
  ld 6, 40(25)
  cmpld 6, 7
  ble L102
  ld 3, 32(25)
  li 10, 15
  and 8, 6, 10
  vmr 11, 7
  lxvb16x 32+9, 0, 3
  vmr 12, 9
  cmpldi 8, 8
  bge L104
  li 10, 8
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrd 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L105
L104:
  cmpldi 8, 8
  bne L106
  mfvsrd 7, 32+9
  li 10, 0
  mtvsrdd 32+9, 7, 10
  b L107
L106:
  li 10, 16
  sub 10, 10, 8
  sldi 10, 10, 3
  mfvsrld 7, 32+9
  srd 7, 7, 10
  sld 7, 7, 10
  mfvsrd 10, 32+9
  mtvsrdd 32+9, 10, 7
L107:
L105:
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  vmr 0, 11
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  vxor 12, 12, 0
  stxvb16x 32+12, 0, 3
  b L103
L102:
L103:
  ld 7, 64(25)
  sldi 6, 6, 3
  sldi 7, 7, 3
  mtvsrdd 32+9, 6, 7
  lxvb16x 32+5, 0, 5
  vspltisw 0, 0
  vsldoi 5, 5, 5, 8
  vsldoi 7, 0, 5, 8
  vsldoi 6, 5, 0, 8
  vxor 9, 1, 9
  vpmsumd 2, 9, 7
  vpmsumd 3, 9, 5
  vpmsumd 4, 9, 6
  vspltisw 8, 0
  lis 10, -15872
  mtvsrws 32+0, 10
  vsldoi 1, 8, 0, 4
  vsldoi 8, 1, 8, 4
  vspltisw 0, 0
  vsldoi 9, 3, 0, 8
  vxor 2, 2, 9
  vsldoi 10, 2, 2, 8
  vpmsumd 2, 2, 8
  vsldoi 3, 0, 3, 8
  vxor 4, 4, 3
  vxor 2, 2, 10
  vsldoi 1, 2, 2, 8
  vpmsumd 2, 2, 8
  vxor 1, 1, 4
  vxor 1, 1, 2
  vmr 7, 21
  vmr 0, 7
  li 10, 0
  lxvb16x 32+2, 10, 4
  vxor 0, 0, 2
  li 10, 16
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 32
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 48
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 64
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 80
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 96
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 112
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 128
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 144
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 160
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 176
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 192
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 208
  lxvb16x 32+2, 10, 4
  vcipher 0, 0, 2
  li 10, 224
  lxvb16x 32+2, 10, 4
  vcipherlast 0, 0, 2
  vxor 2, 2, 2
  vxor 1, 1, 0
  ld 3, 96(25)
  lxvb16x 32+0, 0, 3
  vcmpequw 0, 0, 1
  mfvsrld 4, 32+0
  li 5, 1
  addc 3, 4, 5
  li 3, 0
  adde 3, 3, 3
  xor 3, 5, 3
  mr 6, 3
  mfvsrd 4, 32+0
  li 5, 1
  addc 3, 4, 5
  li 3, 0
  adde 3, 3, 3
  xor 3, 5, 3
  add 3, 6, 3
  ld 25, 0(1)
  ld 26, 8(1)
  ld 27, 16(1)
  ld 28, 24(1)
  ld 29, 32(1)
  ld 30, 40(1)
  ld 31, 48(1)
  lxv 32+20, 64(1)
  lxv 32+21, 80(1)
  addi 1, 1, 96

  blr

.section .note.GNU-stack,"",%progbits
