#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

typedef unsigned __int128 uint128_t;

typedef uint128_t* transpose_t;

static  void to_transpose(transpose_t out, uint8_t* in) {
  for (int i = 0; i < 8; i++) {
    uint128_t u = 0;
    for (int j = 0; j < 128; j++) {
      if (i > j)
	u ^= (uint128_t)(in[j] & ((uint8_t)1 << i)) >> (i - j);
      else
	u ^= (uint128_t)(in[j] & ((uint8_t)1 << i)) << (j - i);
    }
    out[i] = u;
  }
}

static  void to_transpose_block(transpose_t out, uint8_t* in) {
  for (int i = 0; i < 8; i++) {
    uint128_t u = 0;
    for (int j = 0; j < 16; j++) {
      if (i > j)
	u ^= (uint128_t)(in[j] & ((uint8_t)1 << i)) >> (i - j);
      else
	u ^= (uint128_t)(in[j] & ((uint8_t)1 << i)) << (j - i);
    }
    u = u ^ (u << 16);
    u = u ^ (u << 32);
    u = u ^ (u << 64);
    out[i] = u;
  }
}

static  void from_transpose(uint8_t* out, transpose_t in) {
  for (int i = 0; i < 128; i++) {
    uint8_t r = 0;
    for (int j = 0; j < 8; j++) {
      if (i > j)
	r ^= (uint8_t)((uint128_t)(in[j] & ((uint128_t)1 << i)) >> (i - j));
      else
	r ^= (uint8_t)((uint128_t)(in[j] & ((uint128_t)1 << i)) << (j - i));
    }
    out[i] = r;
  }
}

static void subBytes(transpose_t st) {
  uint128_t u0 = st[7];
  uint128_t u1 = st[6];
  uint128_t u2 = st[5];
  uint128_t u3 = st[4];
  uint128_t u4 = st[3];
  uint128_t u5 = st[2];
  uint128_t u6 = st[1];
  uint128_t u7 = st[0];

  uint128_t t1 = u6 ^ u4; 
  uint128_t t2 = u3 ^ u0;
  uint128_t t3 = u1 ^ u2;
  uint128_t t6 = u1 ^ u5; 
  uint128_t t7 = u0 ^ u6; 
  uint128_t t13 = u2 ^ u5; 
  uint128_t t16 = u0 ^ u5;
  uint128_t t18 = u6 ^ u5;
  
  uint128_t t4 = u7 ^ t3;
  uint128_t t5 = t1 ^ t2; 
  uint128_t t8 = t1 ^ t6;
  uint128_t t9 = u6 ^ t4;
    
  uint128_t t10 = u3 ^ t4;
  uint128_t t11 = u7 ^ t5;
  uint128_t t12 = t5 ^ t6;
  uint128_t t14 = t3 ^ t5;
  uint128_t t15 = u5 ^ t7; 
  uint128_t t17 = u7 ^ t8;  
  uint128_t t19 = t2 ^ t18;
  uint128_t t22 = u0 ^ t4;
  uint128_t t54 = t2 & t8;
  uint128_t t50 = t9 & t4;
    
  uint128_t t20 = t4 ^ t15; 
  uint128_t t21 = t1 ^ t13;
  uint128_t t39 = t21 ^ t5;
  uint128_t t40 = t21 ^ t7;  
  uint128_t t41 = t7 ^ t19;
  uint128_t t42 = t16 ^ t14;
  uint128_t t43 = t22 ^ t17;
  uint128_t t44 = t19 & t5;
  uint128_t t45 = t20 & t11;
  uint128_t t47 = t10 & u7;
  uint128_t t57 = t16 & t14;
  
  uint128_t t46 = t12 ^ t44;  
  uint128_t t48 = t47 ^ t44;
  uint128_t t49 = t7 & t21;
  uint128_t t51 = t40 ^ t49;
  uint128_t t52 = t22 & t17;
  uint128_t t53 = t52 ^ t49;

  uint128_t t55 = t41 & t39;
  uint128_t t56 = t55 ^ t54;
  uint128_t t58 = t57 ^ t54;
  uint128_t t59 = t46 ^ t45;
  uint128_t t60 = t48 ^ t42;
  uint128_t t61 = t51 ^ t50;
  uint128_t t62 = t53 ^ t58;
  uint128_t t63 = t59 ^ t56;
  uint128_t t64 = t60 ^ t58;
  uint128_t t65 = t61 ^ t56;
  uint128_t t66 = t62 ^ t43;
  uint128_t t67 = t65 ^ t66; 
  uint128_t t68 = t65 & t63;
  uint128_t t69 = t64 ^ t68;
  uint128_t t70 = t63 ^ t64;
  uint128_t t71 = t66 ^ t68; 
  uint128_t t72 = t71 & t70;
  uint128_t t73 = t69 & t67;
  uint128_t t74 = t63 & t66;
  uint128_t t75 = t70 & t74;
  uint128_t t76 = t70 ^ t68;
  uint128_t t77 = t64 & t65;
  uint128_t t78 = t67 & t77;
  uint128_t t79 = t67 ^ t68;
  uint128_t t80 = t64 ^ t72;
  uint128_t t81 = t75 ^ t76;
  uint128_t t82 = t66 ^ t73;
  uint128_t t83 = t78 ^ t79;
  uint128_t t84 = t81 ^ t83;
  uint128_t t85 = t80 ^ t82;
  uint128_t t86 = t80 ^ t81;
  uint128_t t87 = t82 ^ t83;
  uint128_t t88 = t85 ^ t84;
  uint128_t t89 = t87 & t5;
  uint128_t t90 = t83 & t11;
  uint128_t t91 = t82 & u7;
  uint128_t t92 = t86 & t21;
  uint128_t t93 = t81 & t4;
  uint128_t t94 = t80 & t17;
  uint128_t t95 = t85 & t8;
  uint128_t t96 = t88 & t39;
  uint128_t t97 = t84 & t14;
  uint128_t t98 = t87 & t19;
  uint128_t t99 = t83 & t20;
  uint128_t t100 = t82 & t10;
  uint128_t t101 = t86 & t7;
  uint128_t t102 = t81 & t9;
  uint128_t t103 = t80 & t22;
  uint128_t t104 = t85 & t2;
  uint128_t t105 = t88 & t41;
  uint128_t t106 = t84 & t16;
  uint128_t t107 = t104 ^ t105;
  uint128_t t108 = t93 ^ t99;
  uint128_t t109 = t96 ^ t107;
  uint128_t t110 = t98 ^ t108;
  uint128_t t111 = t91 ^ t101;
  uint128_t t112 = t89 ^ t92;
  uint128_t t113 = t107 ^ t112;
  uint128_t t114 = t90 ^ t110;
  uint128_t t115 = t89 ^ t95;
  uint128_t t116 = t94 ^ t102;
  uint128_t t117 = t97 ^ t103 ;
  uint128_t t118 = t91 ^ t114;
  uint128_t t119 = t111 ^ t117;
  uint128_t t120 = t100 ^ t108;
  uint128_t t121 = t92 ^ t95;
  uint128_t t122 = t110 ^ t121;
  uint128_t t123 = t106 ^ t119;
  uint128_t t124 = t104 ^ t115;
  uint128_t t125 = t111 ^ t116;
  st[7] = t109 ^ t122;
  st[5] = ~(t123 ^ t124);
  uint128_t t128 = t94 ^ t107;
  st[4] = t113 ^ t114;
  st[3] = t118 ^ t128;
  uint128_t t131 = t93 ^ t101;
  uint128_t t132 = t112 ^ t120;
  st[0] = ~(t113 ^ t125);
  uint128_t t134 = t97 ^ t116;
  uint128_t t135 = t131 ^ t134;
  uint128_t t136 = t93 ^ t115;
  st[1] = ~(t109 ^ t135);
  uint128_t t138 = t119 ^ t132;
  st[2] = t109 ^ t138;
  uint128_t t140 = t114 ^ t136;
  st[6] = ~(t109 ^ t140); 
}

static const uint128_t row_maskr[4]  = {
  0x1111111111111111,
  0x1110111011101110,
  0x1100110011001100,
  0x1000100010001000
};

static const uint64_t row_maskl[4]  = {
  0x1111111111111111,
  0x0001000100010001,
  0x0011001100110011,
  0x0111011101110111
};

static const uint64_t col_mask[4]  = {
  0x000f000f000f000f,
  0x00ff00ff00ff00ff,
  0x0fff0fff0fff0fff,
};

static  void shiftRow(int i, int shift, transpose_t st){
  uint128_t rm = (uint128_t)row_maskr[shift] << i;
  rm ^= rm << 64;
  uint128_t lm = (uint128_t)row_maskl[shift] << i;
  lm ^= lm << 64;
  uint128_t st_mask = (uint128_t)row_maskr[0] << i;
  st_mask ^= st_mask << 64;
  uint128_t nst_mask = ~st_mask;
  int sh = 4 * shift;
  for (int i = 0; i < 8; i++) {
    uint128_t row1 = st[i] & rm;
    uint128_t row2 = st[i] & lm;
    row1 = (row1 >> sh) | (row2 << (16 - sh));
    st[i] = (st[i] & nst_mask) ^ row1;
  }
}

static  void shiftRows(transpose_t st) {
  shiftRow(1,1,st);
  shiftRow(2,2,st);
  shiftRow(3,3,st);
}

static  void xtime(transpose_t st) {
  uint128_t prev = st[0];
  for (int i = 0; i < 7; i++) {
    uint128_t p = st[i+1];
    st[i+1] = prev;
    prev = p;
  }
  st[0] = prev;
  st[1] ^= prev;
  st[3] ^= prev;
  st[4] ^= prev;
}  

static void mixColumn(int c, transpose_t st) {
  uint128_t st_mask = (uint128_t)col_mask[0] << (4 * c);
  st_mask ^= st_mask << 64;
  uint128_t nst_mask = ~st_mask;
  uint128_t st1[8] = {0};
  uint128_t st2[8] = {0};
  for (int i = 0; i < 8; i++) {
    uint128_t col = st[i] & st_mask;
    uint128_t col1 = ((uint128_t)(col >> 1) | (uint128_t)(col << 3)) & st_mask;
    uint128_t col2 = ((uint128_t)(col >> 2) | (uint128_t)(col << 2)) & st_mask;
    uint128_t col3 = ((uint128_t)(col >> 3) | (uint128_t)(col << 1)) & st_mask;
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

static  void rounds(transpose_t st, uint128_t* key) {
  for (int i = 0; i < 9; i++)
    aes_enc(st,key+(8*i));
}

static void block_cipher(uint8_t* out, uint8_t* in, uint128_t* key) {
  uint128_t st[8] = {0};
  to_transpose(st,in);
  uint128_t* k0 = key;
  uint128_t* k = key + 8;
  uint128_t* kn = key + (8 * 10);
  addRoundKey(st,k0);
  rounds(st,k);
  aes_enc_last(st,kn);
  from_transpose(out,st);
}

static uint8_t rcon[11] = {
  (0x8d), (0x01), (0x02), (0x04), (0x08), (0x10), (0x20), (0x40), (0x80), (0x1b), (0x36)
};

static void key_expansion_step(transpose_t next, transpose_t prev, uint8_t rcon) {
  uint128_t mask0 = (uint128_t)col_mask[0];
  mask0 ^= mask0 << 64;
  uint128_t mask1 = (uint128_t)col_mask[1];
  mask1 ^= mask1 << 64;
  uint128_t mask2 = (uint128_t)col_mask[2];
  mask2 ^= mask2 << 64;
  //  uint128_t mask3 = col_maskl[3];
  //mask3 ^= mask3 << 64;
  
  memcpy((uint8_t*)next,(uint8_t*)prev,128);
  subBytes(next);
  for (int i = 0; i < 8; i++) {
    uint128_t n = (next[i] & (mask0 << 24)) >> 12;
    n = (n >> 1 | n << 3) & mask0;
    uint128_t ri = (uint128_t)((rcon >> i) & (uint8_t)1);
    n ^= (ri ^ (ri << 16) ^ (ri << 32) ^ (ri << 48)
	  ^ (ri << 64) ^ (ri << 80) ^ (ri << 96) ^ (ri << 112));
    n ^= (n << 4) ^ (n << 8) ^ (n << 12);
    uint128_t p = prev[i];
    p ^= ((p & mask2) << 4) ^ ((p & mask1) << 8)
      ^ ((p & mask0) << 12);
    next[i] = n ^ p;
  }
}
			
static void key_expansion(uint128_t* out, uint8_t* key) {
  to_transpose_block(out,key);
  for (int i = 1; i < 11; i++)
    key_expansion_step(out+(8*i),out+(8*i-8),rcon[i]);
}

static void aes128_block(uint8_t* out, uint128_t* kex, uint8_t* n, uint32_t c) {
  uint8_t in[128] = {0};
  uint8_t* curr = in;
  for (int i = 0; i < 8; i++) {
    memcpy(curr,n,12);
    curr[12] = (uint8_t)(c >> 24);
    curr[13] = (uint8_t)(c >> 16);
    curr[14] = (uint8_t)(c >> 8);
    curr[15] = (uint8_t)(c);
    c = c + 1;
    curr = curr + 16;
  }
  block_cipher(out,in,kex);
}

static void aes128_ctr(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {

  uint128_t kex[8*11] = {0};
  key_expansion(kex,k);

  uint8_t kb[128] = {0};
  int blocks128 = in_len / 128;
  for (int i = 0; i < blocks128; i++) {
    aes128_block(kb,kex,n,c+(8*i));
    for (int j = 0; j < 128; j++)
      out[(128*i)+j] = in[(128*i)+j] ^ kb[j];
  }

  int rem = in_len % 128;
  if (rem > 0) {
    out = out + (128 * blocks128);
    in  = in + (128 * blocks128);
    c = c + (8 * blocks128);
    aes128_block(kb,kex,n,c);
    for (int j = 0; j < rem; j++)
      out[j] = in[j] ^ kb[j];
  }
}

void aes128_encrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}

void aes128_decrypt(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {
  aes128_ctr(out,in,in_len,k,n,c);
}

