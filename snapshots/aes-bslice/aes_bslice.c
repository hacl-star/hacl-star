#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

typedef uint8_t* state_t;
typedef uint16_t* transpose_t;

static  void to_transpose(transpose_t out, state_t in) {
  memset(out,0,16);
  for (int i = 0; i < 8; i++)
    for (int j = 0; j < 16; j++)
      if (i > j)
	out[i] ^= (uint16_t)(in[j] & ((uint8_t)1 << i)) >> (i - j);
      else
	out[i] ^= (uint16_t)(in[j] & ((uint8_t)1 << i)) << (j - i);
}

static  void from_transpose(state_t out, transpose_t in) {
  memset(out,0,16);
  for (int i = 0; i < 16; i++)
    for (int j = 0; j < 8; j++)
      if (i > j)
	out[i] ^= (uint8_t)((uint16_t)(in[j] & ((uint16_t)1 << i)) >> (i - j));
      else
	out[i] ^= (uint8_t)((uint16_t)(in[j] & ((uint16_t)1 << i)) << (j - i));
}

static void subBytes(transpose_t st) {
  uint16_t u0 = st[7];
  uint16_t u1 = st[6];
  uint16_t u2 = st[5];
  uint16_t u3 = st[4];
  uint16_t u4 = st[3];
  uint16_t u5 = st[2];
  uint16_t u6 = st[1];
  uint16_t u7 = st[0];

  uint16_t t1 = u6 ^ u4; 
  uint16_t t2 = u3 ^ u0;
  uint16_t t3 = u1 ^ u2;
  uint16_t t6 = u1 ^ u5; 
  uint16_t t7 = u0 ^ u6; 
  uint16_t t13 = u2 ^ u5; 
  uint16_t t16 = u0 ^ u5;
  uint16_t t18 = u6 ^ u5;
  
  uint16_t t4 = u7 ^ t3;
  uint16_t t5 = t1 ^ t2; 
  uint16_t t8 = t1 ^ t6;
  uint16_t t9 = u6 ^ t4;
    
  uint16_t t10 = u3 ^ t4;
  uint16_t t11 = u7 ^ t5;
  uint16_t t12 = t5 ^ t6;
  uint16_t t14 = t3 ^ t5;
  uint16_t t15 = u5 ^ t7; 
  uint16_t t17 = u7 ^ t8;  
  uint16_t t19 = t2 ^ t18;
  uint16_t t22 = u0 ^ t4;
  uint16_t t54 = t2 & t8;
  uint16_t t50 = t9 & t4;
    
  uint16_t t20 = t4 ^ t15; 
  uint16_t t21 = t1 ^ t13;
  uint16_t t39 = t21 ^ t5;
  uint16_t t40 = t21 ^ t7;  
  uint16_t t41 = t7 ^ t19;
  uint16_t t42 = t16 ^ t14;
  uint16_t t43 = t22 ^ t17;
  uint16_t t44 = t19 & t5;
  uint16_t t45 = t20 & t11;
  uint16_t t47 = t10 & u7;
  uint16_t t57 = t16 & t14;
  
  uint16_t t46 = t12 ^ t44;  
  uint16_t t48 = t47 ^ t44;
  uint16_t t49 = t7 & t21;
  uint16_t t51 = t40 ^ t49;
  uint16_t t52 = t22 & t17;
  uint16_t t53 = t52 ^ t49;

  uint16_t t55 = t41 & t39;
  uint16_t t56 = t55 ^ t54;
  uint16_t t58 = t57 ^ t54;
  uint16_t t59 = t46 ^ t45;
  uint16_t t60 = t48 ^ t42;
  uint16_t t61 = t51 ^ t50;
  uint16_t t62 = t53 ^ t58;
  uint16_t t63 = t59 ^ t56;
  uint16_t t64 = t60 ^ t58;
  uint16_t t65 = t61 ^ t56;
  uint16_t t66 = t62 ^ t43;
  uint16_t t67 = t65 ^ t66; 
  uint16_t t68 = t65 & t63;
  uint16_t t69 = t64 ^ t68;
  uint16_t t70 = t63 ^ t64;
  uint16_t t71 = t66 ^ t68; 
  uint16_t t72 = t71 & t70;
  uint16_t t73 = t69 & t67;
  uint16_t t74 = t63 & t66;
  uint16_t t75 = t70 & t74;
  uint16_t t76 = t70 ^ t68;
  uint16_t t77 = t64 & t65;
  uint16_t t78 = t67 & t77;
  uint16_t t79 = t67 ^ t68;
  uint16_t t80 = t64 ^ t72;
  uint16_t t81 = t75 ^ t76;
  uint16_t t82 = t66 ^ t73;
  uint16_t t83 = t78 ^ t79;
  uint16_t t84 = t81 ^ t83;
  uint16_t t85 = t80 ^ t82;
  uint16_t t86 = t80 ^ t81;
  uint16_t t87 = t82 ^ t83;
  uint16_t t88 = t85 ^ t84;
  uint16_t t89 = t87 & t5;
  uint16_t t90 = t83 & t11;
  uint16_t t91 = t82 & u7;
  uint16_t t92 = t86 & t21;
  uint16_t t93 = t81 & t4;
  uint16_t t94 = t80 & t17;
  uint16_t t95 = t85 & t8;
  uint16_t t96 = t88 & t39;
  uint16_t t97 = t84 & t14;
  uint16_t t98 = t87 & t19;
  uint16_t t99 = t83 & t20;
  uint16_t t100 = t82 & t10;
  uint16_t t101 = t86 & t7;
  uint16_t t102 = t81 & t9;
  uint16_t t103 = t80 & t22;
  uint16_t t104 = t85 & t2;
  uint16_t t105 = t88 & t41;
  uint16_t t106 = t84 & t16;
  uint16_t t107 = t104 ^ t105;
  uint16_t t108 = t93 ^ t99;
  uint16_t t109 = t96 ^ t107;
  uint16_t t110 = t98 ^ t108;
  uint16_t t111 = t91 ^ t101;
  uint16_t t112 = t89 ^ t92;
  uint16_t t113 = t107 ^ t112;
  uint16_t t114 = t90 ^ t110;
  uint16_t t115 = t89 ^ t95;
  uint16_t t116 = t94 ^ t102;
  uint16_t t117 = t97 ^ t103 ;
  uint16_t t118 = t91 ^ t114;
  uint16_t t119 = t111 ^ t117;
  uint16_t t120 = t100 ^ t108;
  uint16_t t121 = t92 ^ t95;
  uint16_t t122 = t110 ^ t121;
  uint16_t t123 = t106 ^ t119;
  uint16_t t124 = t104 ^ t115;
  uint16_t t125 = t111 ^ t116;
  st[7] = t109 ^ t122;
  st[5] = ~(t123 ^ t124);
  uint16_t t128 = t94 ^ t107;
  st[4] = t113 ^ t114;
  st[3] = t118 ^ t128;
  uint16_t t131 = t93 ^ t101;
  uint16_t t132 = t112 ^ t120;
  st[0] = ~(t113 ^ t125);
  uint16_t t134 = t97 ^ t116;
  uint16_t t135 = t131 ^ t134;
  uint16_t t136 = t93 ^ t115;
  st[1] = ~(t109 ^ t135);
  uint16_t t138 = t119 ^ t132;
  st[2] = t109 ^ t138;
  uint16_t t140 = t114 ^ t136;
  st[6] = ~(t109 ^ t140); 
}

static  void shiftRow(int i, int shift, transpose_t st){
  uint16_t st_mask = (uint16_t)0x1111 << i;
  uint16_t nst_mask = ~st_mask;
  int sh = 4 * shift;
  for (int i = 0; i < 8; i++) {
    uint16_t row = st[i] & st_mask;
    row = (row >> sh) | (row << (16 - sh));
    st[i] = (st[i] & nst_mask) ^ row;
  }
}

static  void shiftRows(transpose_t st) {
  shiftRow(1,1,st);
  shiftRow(2,2,st);
  shiftRow(3,3,st);
}

static  void xtime(transpose_t st) {
  uint16_t prev = st[0];
  for (int i = 0; i < 7; i++) {
    uint16_t p = st[i+1];
    st[i+1] = prev;
    prev = p;
  }
  st[0] = prev;
  st[1] ^= prev;
  st[3] ^= prev;
  st[4] ^= prev;
}  

static  void mixColumn(int c, transpose_t st) {
  uint16_t st_mask = (uint16_t)0xf << (4 * c);
  uint16_t nst_mask = ~st_mask;
  uint16_t st1[8] = {0};
  uint16_t st2[8] = {0};
  for (int i = 0; i < 8; i++) {
    uint16_t col = st[i] & st_mask;
    uint16_t col1 = ((uint16_t)(col >> 1) | (uint16_t)(col << 3)) & st_mask;
    uint16_t col2 = ((uint16_t)(col >> 2) | (uint16_t)(col << 2)) & st_mask;
    uint16_t col3 = ((uint16_t)(col >> 3) | (uint16_t)(col << 1)) & st_mask;
    st1[i] = col ^ col1;
    st2[i] = col1 ^ col2 ^ col3;
  }
  xtime(st1);
  for (int i = 0; i < 8; i++) 
    st[i] = (st[i] & nst_mask) ^ st2[i] ^ st1[i];
}

static  void mixColumns(transpose_t st) {
  mixColumn(0,st);
  mixColumn(1,st);
  mixColumn(2,st);
  mixColumn(3,st);
}

static  void addRoundKey(transpose_t st, transpose_t k) {
  for (int i = 0; i < 8; i++)
    st[i] ^= k[i];
}

static  void aes_enc(transpose_t st, transpose_t k) {
  subBytes(st);
  shiftRows(st);
  mixColumns(st);
  addRoundKey(st,k);
}

static  void aes_enc_last(transpose_t st, transpose_t k) {
  subBytes(st);
  shiftRows(st);
  addRoundKey(st,k);
}

static  void rounds(transpose_t st, uint16_t* key) {
  for (int i = 0; i < 9; i++)
    aes_enc(st,key+(8*i));
}

static void block_cipher(state_t out, state_t in, uint16_t* key) {
  uint16_t st[8] = {0};
  to_transpose(st,in);
  uint16_t* k0 = key;
  uint16_t* k = key + 8;
  uint16_t* kn = key + (8 * 10);
  addRoundKey(st,k0);
  rounds(st,k);
  aes_enc_last(st,kn);
  from_transpose(out,st);
}

static uint8_t rcon[11] = {
  (0x8d), (0x01), (0x02), (0x04), (0x08), (0x10), (0x20), (0x40), (0x80), (0x1b), (0x36)
};

static void key_expansion_step(transpose_t next, transpose_t prev, uint8_t rcon) {
  memcpy((uint8_t*)next,(uint8_t*)prev,16);
  subBytes(next);
  for (int i = 0; i < 8; i++) {
    uint16_t n = next[i] >> 12;
    n = (n >> 1 | n << 3) & 0xf;
    n ^= (uint16_t)((rcon >> i) & (uint8_t)1);
    n ^= (n << 4) ^ (n << 8) ^ (n << 12);
    uint16_t p = prev[i];
    p ^= (p << 4) ^ (p << 8) ^ (p << 12);
    next[i] = n ^ p;
  }
}
			
static void key_expansion(uint16_t* out, state_t key) {
  to_transpose(out,key);
  for (int i = 1; i < 11; i++)
    key_expansion_step(out+(8*i),out+(8*i-8),rcon[i]);
}

static void aes128_block(state_t out,uint16_t* kex, uint8_t* n, uint32_t c) {
  uint8_t in[16] = {0};
  memcpy(in,n,12);
  in[12] = (uint8_t)(c >> 24);
  in[13] = (uint8_t)(c >> 16);
  in[14] = (uint8_t)(c >> 8);
  in[15] = (uint8_t)(c);
  block_cipher(out,in,kex);
}

static void aes128_ctr(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {

  uint16_t kex[8*11] = {0};
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

