#include <inttypes.h>
#include <stdlib.h> 
#include <string.h> 
#include <sys/types.h> 

typedef uint64_t* transpose_t;

//#define static static inline __attribute((always_inline))

static  void to_transpose(transpose_t out, uint8_t* in) {
  for (int i = 0; i < 8; i++) {
    uint64_t u = 0;
    for (int j = 0; j < 64; j++) {
      if (i > j)
	u ^= (uint64_t)(in[j] & ((uint8_t)1 << i)) >> (i - j);
      else
	u ^= (uint64_t)(in[j] & ((uint8_t)1 << i)) << (j - i);
    }
    out[i] = u;
  }
}

static  void to_transpose_block(transpose_t out, uint8_t* in) {
  for (int i = 0; i < 8; i++) {
    uint64_t u = 0;
    for (int j = 0; j < 16; j++) {
       if (i > j)
	u ^= (uint64_t)(in[j] & ((uint8_t)1 << i)) >> (i - j);
      else
	u ^= (uint64_t)(in[j] & ((uint8_t)1 << i)) << (j - i);
    }
    u ^= u << 16;
    u ^= u << 32;
    out[i] = u;
  }
}

static void from_transpose(uint8_t* out, transpose_t in) {
  for (int i = 0; i < 64; i++) {
    uint8_t u = 0;
    for (int j = 0; j < 8; j++) {
      if (i > j)
	u ^= (uint8_t)((uint64_t)(in[j] & ((uint64_t)1 << i)) >> (i - j));
      else
	u ^= (uint8_t)((uint64_t)(in[j] & ((uint64_t)1 << i)) << (j - i));
    }
    out[i] = u;
  }
}

static void subBytes(transpose_t st) {
  uint64_t u0 = st[7];
  uint64_t u1 = st[6];
  uint64_t u2 = st[5];
  uint64_t u3 = st[4];
  uint64_t u4 = st[3];
  uint64_t u5 = st[2];
  uint64_t u6 = st[1];
  uint64_t u7 = st[0];

  uint64_t t1 = u6 ^ u4; 
  uint64_t t2 = u3 ^ u0;
  uint64_t t3 = u1 ^ u2;
  uint64_t t6 = u1 ^ u5; 
  uint64_t t7 = u0 ^ u6; 
  uint64_t t13 = u2 ^ u5; 
  uint64_t t16 = u0 ^ u5;
  uint64_t t18 = u6 ^ u5;
  
  uint64_t t4 = u7 ^ t3;
  uint64_t t5 = t1 ^ t2; 
  uint64_t t8 = t1 ^ t6;
  uint64_t t9 = u6 ^ t4;
    
  uint64_t t10 = u3 ^ t4;
  uint64_t t11 = u7 ^ t5;
  uint64_t t12 = t5 ^ t6;
  uint64_t t14 = t3 ^ t5;
  uint64_t t15 = u5 ^ t7; 
  uint64_t t17 = u7 ^ t8;  
  uint64_t t19 = t2 ^ t18;
  uint64_t t22 = u0 ^ t4;
  uint64_t t54 = t2 & t8;
  uint64_t t50 = t9 & t4;
    
  uint64_t t20 = t4 ^ t15; 
  uint64_t t21 = t1 ^ t13;
  uint64_t t39 = t21 ^ t5;
  uint64_t t40 = t21 ^ t7;  
  uint64_t t41 = t7 ^ t19;
  uint64_t t42 = t16 ^ t14;
  uint64_t t43 = t22 ^ t17;
  uint64_t t44 = t19 & t5;
  uint64_t t45 = t20 & t11;
  uint64_t t47 = t10 & u7;
  uint64_t t57 = t16 & t14;
  
  uint64_t t46 = t12 ^ t44;  
  uint64_t t48 = t47 ^ t44;
  uint64_t t49 = t7 & t21;
  uint64_t t51 = t40 ^ t49;
  uint64_t t52 = t22 & t17;
  uint64_t t53 = t52 ^ t49;

  uint64_t t55 = t41 & t39;
  uint64_t t56 = t55 ^ t54;
  uint64_t t58 = t57 ^ t54;
  uint64_t t59 = t46 ^ t45;
  uint64_t t60 = t48 ^ t42;
  uint64_t t61 = t51 ^ t50;
  uint64_t t62 = t53 ^ t58;
  uint64_t t63 = t59 ^ t56;
  uint64_t t64 = t60 ^ t58;
  uint64_t t65 = t61 ^ t56;
  uint64_t t66 = t62 ^ t43;
  uint64_t t67 = t65 ^ t66; 
  uint64_t t68 = t65 & t63;
  uint64_t t69 = t64 ^ t68;
  uint64_t t70 = t63 ^ t64;
  uint64_t t71 = t66 ^ t68; 
  uint64_t t72 = t71 & t70;
  uint64_t t73 = t69 & t67;
  uint64_t t74 = t63 & t66;
  uint64_t t75 = t70 & t74;
  uint64_t t76 = t70 ^ t68;
  uint64_t t77 = t64 & t65;
  uint64_t t78 = t67 & t77;
  uint64_t t79 = t67 ^ t68;
  uint64_t t80 = t64 ^ t72;
  uint64_t t81 = t75 ^ t76;
  uint64_t t82 = t66 ^ t73;
  uint64_t t83 = t78 ^ t79;
  uint64_t t84 = t81 ^ t83;
  uint64_t t85 = t80 ^ t82;
  uint64_t t86 = t80 ^ t81;
  uint64_t t87 = t82 ^ t83;
  uint64_t t88 = t85 ^ t84;
  uint64_t t89 = t87 & t5;
  uint64_t t90 = t83 & t11;
  uint64_t t91 = t82 & u7;
  uint64_t t92 = t86 & t21;
  uint64_t t93 = t81 & t4;
  uint64_t t94 = t80 & t17;
  uint64_t t95 = t85 & t8;
  uint64_t t96 = t88 & t39;
  uint64_t t97 = t84 & t14;
  uint64_t t98 = t87 & t19;
  uint64_t t99 = t83 & t20;
  uint64_t t100 = t82 & t10;
  uint64_t t101 = t86 & t7;
  uint64_t t102 = t81 & t9;
  uint64_t t103 = t80 & t22;
  uint64_t t104 = t85 & t2;
  uint64_t t105 = t88 & t41;
  uint64_t t106 = t84 & t16;
  uint64_t t107 = t104 ^ t105;
  uint64_t t108 = t93 ^ t99;
  uint64_t t109 = t96 ^ t107;
  uint64_t t110 = t98 ^ t108;
  uint64_t t111 = t91 ^ t101;
  uint64_t t112 = t89 ^ t92;
  uint64_t t113 = t107 ^ t112;
  uint64_t t114 = t90 ^ t110;
  uint64_t t115 = t89 ^ t95;
  uint64_t t116 = t94 ^ t102;
  uint64_t t117 = t97 ^ t103 ;
  uint64_t t118 = t91 ^ t114;
  uint64_t t119 = t111 ^ t117;
  uint64_t t120 = t100 ^ t108;
  uint64_t t121 = t92 ^ t95;
  uint64_t t122 = t110 ^ t121;
  uint64_t t123 = t106 ^ t119;
  uint64_t t124 = t104 ^ t115;
  uint64_t t125 = t111 ^ t116;
  st[7] = t109 ^ t122;
  st[5] = ~(t123 ^ t124);
  uint64_t t128 = t94 ^ t107;
  st[4] = t113 ^ t114;
  st[3] = t118 ^ t128;
  uint64_t t131 = t93 ^ t101;
  uint64_t t132 = t112 ^ t120;
  st[0] = ~(t113 ^ t125);
  uint64_t t134 = t97 ^ t116;
  uint64_t t135 = t131 ^ t134;
  uint64_t t136 = t93 ^ t115;
  st[1] = ~(t109 ^ t135);
  uint64_t t138 = t119 ^ t132;
  st[2] = t109 ^ t138;
  uint64_t t140 = t114 ^ t136;
  st[6] = ~(t109 ^ t140); 
}

const uint64_t maskr[3]  = {
  0x1110111011101110,
  0x1100110011001100,
  0x1000100010001000
};

const uint64_t maskl[3]  = {
  0x0001000100010001,
  0x0011001100110011,
  0x0111011101110111 
};

static  void shiftRow(int i, int shift, transpose_t st){
  uint64_t rm = maskr[shift-1] << i;
  uint64_t lm = maskl[shift-1] << i;
  uint64_t st_mask = (uint64_t)0x1111111111111111 << i;
  uint64_t nst_mask = ~st_mask;
  int sh = 4 * shift;
  for (int i = 0; i < 8; i++) {
    uint64_t row1 = st[i] & rm;
    uint64_t row2 = st[i] & lm;
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
  uint64_t prev = st[0];
  for (int i = 0; i < 7; i++) {
    uint64_t p = st[i+1];
    st[i+1] = prev;
    prev = p;
  }
  st[0] = prev;
  st[1] ^= prev;
  st[3] ^= prev;
  st[4] ^= prev;
}  

static void mixColumn(int c, transpose_t st) {
  uint64_t st_mask = (uint64_t)0x000f000f000f000f << (4 * c);
  uint64_t nst_mask = ~st_mask;
  uint64_t st1[8] = {0};
  uint64_t st2[8] = {0};
  for (int i = 0; i < 8; i++) {
    uint64_t col = st[i] & st_mask;
    uint64_t col1 = ((uint64_t)(col >> 1) | (uint64_t)(col << 3)) & st_mask;
    uint64_t col2 = ((uint64_t)(col >> 2) | (uint64_t)(col << 2)) & st_mask;
    uint64_t col3 = ((uint64_t)(col >> 3) | (uint64_t)(col << 1)) & st_mask;
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

static  void rounds(transpose_t st, uint64_t* key) {
  for (int i = 0; i < 9; i++)
    aes_enc(st,key+(8*i));
}

static void block_cipher(uint8_t* out, uint8_t* in, uint64_t* key) {
  uint64_t st[8] = {0};
  to_transpose(st,in);
  uint64_t* k0 = key;
  uint64_t* k = key + 8;
  uint64_t* kn = key + (8 * 10);
  addRoundKey(st,k0);
  rounds(st,k);
  aes_enc_last(st,kn);
  from_transpose(out,st);
}

const uint8_t rcon[11] = {
  (0x8d), (0x01), (0x02), (0x04), (0x08), (0x10), (0x20), (0x40), (0x80), (0x1b), (0x36)
};

static void key_expansion_step(transpose_t next, transpose_t prev, uint8_t rcon) {
  memcpy((uint8_t*)next,(uint8_t*)prev,64);
  subBytes(next);
  for (int i = 0; i < 8; i++) {
    uint64_t n = (next[i] & 0xf000f000f000f000) >> 12;
    n = (n >> 1 | n << 3) & 0x000f000f000f000f;
    uint64_t ri = (uint64_t)((rcon >> i) & (uint8_t)1);
    ri ^= ri << 16;
    ri ^= ri << 32;
    n ^= ri;
    n ^= (n << 4);
    n ^= (n << 8);
    uint64_t p = prev[i];
    p ^= ((p & 0x0fff0fff0fff0fff) << 4) ^ ((p & 0x00ff00ff00ff00ff) << 8)
      ^ ((p & 0x000f000f000f000f) << 12);
    next[i] = n ^ p;
  }
}
			
static void key_expansion(uint64_t* out, uint8_t* key) {
  to_transpose_block(out,key);
  for (int i = 1; i < 11; i++)
    key_expansion_step(out+(8*i),out+(8*i-8),rcon[i]);
}

static void aes128_block(uint8_t* out, uint64_t* kex, uint8_t* n, uint32_t c) {
  uint8_t in[64] = {0};
  uint8_t* curr = in;
  memcpy(curr,n,12);
  curr[12] = (uint8_t)(c >> 24);
  curr[13] = (uint8_t)(c >> 16);
  curr[14] = (uint8_t)(c >> 8);
  curr[15] = (uint8_t)(c);
  c = c + 1;
  curr = curr + 16;
  memcpy(curr,n,12);
  curr[12] = (uint8_t)(c >> 24);
  curr[13] = (uint8_t)(c >> 16);
  curr[14] = (uint8_t)(c >> 8);
  curr[15] = (uint8_t)(c);
  c = c + 1;
  curr = curr + 16;
  memcpy(curr,n,12);
  curr[12] = (uint8_t)(c >> 24);
  curr[13] = (uint8_t)(c >> 16);
  curr[14] = (uint8_t)(c >> 8);
  curr[15] = (uint8_t)(c);
  c = c + 1;
  curr = curr + 16;
  memcpy(curr,n,12);
  curr[12] = (uint8_t)(c >> 24);
  curr[13] = (uint8_t)(c >> 16);
  curr[14] = (uint8_t)(c >> 8);
  curr[15] = (uint8_t)(c);
  block_cipher(out,in,kex);
}

static void aes128_ctr(uint8_t* out, uint8_t* in, int in_len, uint8_t* k, uint8_t* n, uint32_t c) {

  uint64_t kex[8*11] = {0};
  key_expansion(kex,k);

  uint8_t kb[64] = {0};
  int blocks64 = in_len / 64;
  for (int i = 0; i < blocks64; i++) {
    aes128_block(kb,kex,n,c+(4*i));
    for (int j = 0; j < 64; j++)
      out[(64*i)+j] = in[(64*i)+j] ^ kb[j];
  }

  int rem = in_len % 64;
  if (rem > 0) {
    out = out + (64 * blocks64);
    in  = in + (64 * blocks64);
    c = c + (4 * blocks64);
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

