#ifndef __LOOPS_H
#define __LOOPS_H

#define rounds(st)                                      \
  for (int i = 0; i < 10; i++) Hacl_Impl_Chacha20_double_round (st)

#define rounds_(st)                                      \
  for (int i = 0; i < 10; i++) Hacl_Impl_Salsa20_double_round (st)

#define sum_states(a,b) \
  for (int i = 0; i < 16; i++) (a)[i] += (b)[i]

#define xor_bytes(a,b,c,l) \
  for (int i = 0; i < (l); i++) (a)[i] = (b)[i] ^ (c)[i]

#endif
