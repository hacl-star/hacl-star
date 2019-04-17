#include <stdint.h>
#include "params.h"

#define Q KYBER_Q
#define LOW ((1U << 13) - 1)
#define V ((1U << 27)/Q + 1)
#define MONT 4088U
#define MONTSQ 5569U
//#define F ((((uint32_t)MONT*MONT % Q) * (Q-1) % Q) * ((Q-1) >> 8) % Q)
#define F ((MONT * (Q-1) % Q) * ((Q-1) >> 8) % Q)

const uint16_t _16xqinv[16] asm ("_16xqinv") __attribute__((aligned(32))) = {57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857, 57857};
const uint16_t _16xq[16] asm ("_16xq") __attribute__((aligned(32))) = {Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q};
const uint16_t _16x4q[16] asm ("_16x4q") __attribute__((aligned(32))) = {4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q, 4*Q};
const uint16_t _16x2q[16] asm ("_16x2q") __attribute__((aligned(32))) = {2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q, 2*Q};
const uint16_t _low_mask[16] asm ("_low_mask") __attribute__((aligned(32))) = {LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW, LOW};
const uint16_t _16xv[16] asm ("_16xv") __attribute__((aligned(32))) = {V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V};
const  uint8_t _vpshufb_idx[32] asm ("_vpshufb_idx") __attribute__((aligned(32))) = {2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13};
const uint16_t _f[16] asm ("_f") __attribute__((aligned(32))) = {F, F, F, F, F, F, F, F, F, F, F, F, F, F, F, F};
const uint16_t _16xmontsq[16] asm ("_16xmontsq") __attribute__((aligned(32))) = {MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ, MONTSQ};
const uint32_t _mask11[8] asm ("_mask11") __attribute__((aligned(32))) = {0x11111111,0x11111111,0x11111111,0x11111111,0x11111111,0x11111111,0x11111111,0x11111111};
const uint32_t _mask0f[8] asm ("_mask0f") __attribute__((aligned(32))) = {0x0f0f0f0f,0x0f0f0f0f,0x0f0f0f0f,0x0f0f0f0f,0x0f0f0f0f,0x0f0f0f0f,0x0f0f0f0f,0x0f0f0f0f};
const uint16_t _lowdword[16] asm ("_lowdword") __attribute__((aligned(32))) = {0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0, 0xffff, 0x0};

#undef Q
#undef F
#undef V
#undef MONT
#undef MONTSQ
#undef LOW
