#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

static uint8_t sbox[256] = {
      (0x63), (0x7C), (0x77), (0x7B), (0xF2), (0x6B), (0x6F), (0xC5), (0x30), (0x01), (0x67), (0x2B), (0xFE), (0xD7), (0xAB), (0x76),
    (0xCA), (0x82), (0xC9), (0x7D), (0xFA), (0x59), (0x47), (0xF0), (0xAD), (0xD4), (0xA2), (0xAF), (0x9C), (0xA4), (0x72), (0xC0),
    (0xB7), (0xFD), (0x93), (0x26), (0x36), (0x3F), (0xF7), (0xCC), (0x34), (0xA5), (0xE5), (0xF1), (0x71), (0xD8), (0x31), (0x15),
    (0x04), (0xC7), (0x23), (0xC3), (0x18), (0x96), (0x05), (0x9A), (0x07), (0x12), (0x80), (0xE2), (0xEB), (0x27), (0xB2), (0x75),
    (0x09), (0x83), (0x2C), (0x1A), (0x1B), (0x6E), (0x5A), (0xA0), (0x52), (0x3B), (0xD6), (0xB3), (0x29), (0xE3), (0x2F), (0x84),
    (0x53), (0xD1), (0x00), (0xED), (0x20), (0xFC), (0xB1), (0x5B), (0x6A), (0xCB), (0xBE), (0x39), (0x4A), (0x4C), (0x58), (0xCF),
    (0xD0), (0xEF), (0xAA), (0xFB), (0x43), (0x4D), (0x33), (0x85), (0x45), (0xF9), (0x02), (0x7F), (0x50), (0x3C), (0x9F), (0xA8),
    (0x51), (0xA3), (0x40), (0x8F), (0x92), (0x9D), (0x38), (0xF5), (0xBC), (0xB6), (0xDA), (0x21), (0x10), (0xFF), (0xF3), (0xD2),
    (0xCD), (0x0C), (0x13), (0xEC), (0x5F), (0x97), (0x44), (0x17), (0xC4), (0xA7), (0x7E), (0x3D), (0x64), (0x5D), (0x19), (0x73),
    (0x60), (0x81), (0x4F), (0xDC), (0x22), (0x2A), (0x90), (0x88), (0x46), (0xEE), (0xB8), (0x14), (0xDE), (0x5E), (0x0B), (0xDB),
    (0xE0), (0x32), (0x3A), (0x0A), (0x49), (0x06), (0x24), (0x5C), (0xC2), (0xD3), (0xAC), (0x62), (0x91), (0x95), (0xE4), (0x79),
    (0xE7), (0xC8), (0x37), (0x6D), (0x8D), (0xD5), (0x4E), (0xA9), (0x6C), (0x56), (0xF4), (0xEA), (0x65), (0x7A), (0xAE), (0x08),
    (0xBA), (0x78), (0x25), (0x2E), (0x1C), (0xA6), (0xB4), (0xC6), (0xE8), (0xDD), (0x74), (0x1F), (0x4B), (0xBD), (0x8B), (0x8A),
    (0x70), (0x3E), (0xB5), (0x66), (0x48), (0x03), (0xF6), (0x0E), (0x61), (0x35), (0x57), (0xB9), (0x86), (0xC1), (0x1D), (0x9E),
    (0xE1), (0xF8), (0x98), (0x11), (0x69), (0xD9), (0x8E), (0x94), (0x9B), (0x1E), (0x87), (0xE9), (0xCE), (0x55), (0x28), (0xDF),
    (0x8C), (0xA1), (0x89), (0x0D), (0xBF), (0xE6), (0x42), (0x68), (0x41), (0x99), (0x2D), (0x0F), (0xB0), (0x54), (0xBB), (0x16)
};

typedef uint8_t* state_t;

 void subBytes(state_t st) {
  for (int i = 0; i < 16; i++)
    st[i] = sbox[st[i]];
}

 void shiftRow(int i, int shift, state_t st){
   uint8_t s0 = st[i + (4 * (shift % 4))];
   uint8_t s1 = st[i + (4 * ((shift + 1) % 4))];
   uint8_t s2 = st[i + (4 * ((shift + 2) % 4))];
   uint8_t s3 = st[i + (4 * ((shift + 3) % 4))];
   st[i] = s0;
   st[i+4] = s1;
   st[i+8] = s2;
   st[i+12] = s3;
}

 void shiftRows(state_t st) {
  shiftRow(1,1,st);
  shiftRow(2,2,st);
  shiftRow(3,3,st);
}

 uint8_t xtime(uint8_t x) {
  uint8_t x1 = x << 1;
  uint8_t x711b = (uint8_t)((x >> 7) & 1) * 0x1b;
  return x1 ^ x711b;
}

 void mixColumn(int c, state_t st) {
  int i0 = 4 * c;
  uint8_t s0 = st[i0];
  uint8_t s1 = st[i0+1];
  uint8_t s2 = st[i0+2];
  uint8_t s3 = st[i0+3];
  uint8_t tmp = s0 ^ s1 ^ s2 ^ s3;
  st[i0]   = s0 ^ tmp ^ xtime(s0 ^ s1);
  st[i0+1] = s1 ^ tmp ^ xtime(s1 ^ s2);
  st[i0+2] = s2 ^ tmp ^ xtime(s2 ^ s3);
  st[i0+3] = s3 ^ tmp ^ xtime(s3 ^ s0);
}

 void mixColumns(state_t st) {
  mixColumn(0,st);
  mixColumn(1,st);
  mixColumn(2,st);
  mixColumn(3,st);
}

 void addRoundKey(state_t st, state_t k) {
  for (int i = 0; i < 16; i++)
    st[i] ^= k[i];
}

 void aes_enc(state_t st, state_t k) {
  subBytes(st);
  shiftRows(st);
  mixColumns(st);
  addRoundKey(st,k);
}

 void aes_enc_last(state_t st, state_t k) {
  subBytes(st);
  shiftRows(st);
  addRoundKey(st,k);
}

void rounds(state_t st, uint8_t* key) {
  for (int i = 0; i < 9; i++)
    aes_enc(st,key+(16*i));
}

 void block_cipher(state_t out, uint8_t* key) {
  uint8_t* k0 = key;
  uint8_t* k = key + 16;
  uint8_t* kn = key + (16 * 10);
  addRoundKey(out,k0);
  rounds(out,k);
  aes_enc_last(out,kn);
}

 void rotate_word(uint8_t* w) {
  uint8_t w0 = w[0];
  w[0] = w[1];
  w[1] = w[2];
  w[2] = w[3];
  w[3] = w0;
}

 void sub_word(uint8_t* w) {
  w[0] = sbox[w[0]];
  w[1] = sbox[w[1]];
  w[2] = sbox[w[2]];
  w[3] = sbox[w[3]];
}

static uint8_t rcon[11] = {
  (0x8d), (0x01), (0x02), (0x04), (0x08), (0x10), (0x20), (0x40), (0x80), (0x1b), (0x36)
};

 void aes_keygen_assist(uint8_t* out, uint8_t rcon){
  rotate_word(out);
  sub_word(out);
  out[0] ^= rcon;
}

 void key_expansion_word(uint8_t* out, uint8_t* w0, uint8_t* w1, int i){
  memcpy(out,w1,4);
  if (i % 4 == 0) 
    aes_keygen_assist(out,rcon[i/4]);
  for (int i = 0; i < 4; i++)
    out[i] ^= w0[i];
}

 void key_expansion(uint8_t* out, state_t key) {
  memcpy(out,key,16);
  for (int i = 4; i < 44; i++) 
    key_expansion_word(out+(4*i),out+((4*i)-16),out+((4*i)-4),i);
 }

 void aes128_block(state_t out,uint8_t* kex, uint8_t* n, uint32_t c) {
  memcpy(out,n,12);
  out[12] = (uint8_t)(c >> 24);
  out[13] = (uint8_t)(c >> 16);
  out[14] = (uint8_t)(c >> 8);
  out[15] = (uint8_t)(c);
  block_cipher(out,kex);
}

void aes128_ctr(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  uint8_t kex[16*11] = {0};
  key_expansion(kex,k);
  uint8_t kb[16] = {0};
  int blocks = in_len / 16;
  for (int i = 0; i < blocks; i++) {
    aes128_block(kb,kex,n,c+i);
    for (int j = 0; j < 16; j++)
      out[(16*i)+j] = in[(16*i)+j] ^ kb[j];
  }
  int rem = in_len % 16;
  if (rem > 0) {
      aes128_block(kb,kex,n,c+blocks);
      for (int j = 0; j < rem; j++)
	out[(16*blocks)+j] = in[(16*blocks)+j] ^ kb[j];
    }
}

void aes128_encrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}

void aes128_decrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}
