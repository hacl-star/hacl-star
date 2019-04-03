#ifndef __LOOPS_H
#define __LOOPS_H

#define rounds2(st1,st2)						\
  for (int i = 0; i < 10; i++) { \
    Hacl_Impl_Chacha20_vec_double_round (st1);\
    Hacl_Impl_Chacha20_vec_double_round (st2);}

#define rounds3(st1,st2,st3)	 \
  for (int i = 0; i < 10; i++) { \
    Hacl_Impl_Chacha20_vec_double_round (st1);\
    Hacl_Impl_Chacha20_vec_double_round (st2);\
    Hacl_Impl_Chacha20_vec_double_round (st3);}
    

#define rounds(st)						\
  for (int i = 0; i < 10; i++) Hacl_Impl_Chacha20_vec_double_round (st)    

#define rounds16(st)						\
  for (int i = 0; i < 10; i++) Hacl_Impl_Chacha20_vec2_double_round (st)    

#define vec_store16(out,st,vecsize)	 \
  for (int i = 0; i < 16; i++) { \
    vec_store_le(out + (i*vecsize),st[i]);}


#define vec_gather16(st,in)		\
  for (int i = 0; i < 16; i++) { \
    vec_gather(in + (4*i)); }

    
#define vec_xor16(out,in,st,vecsize)		\
  for (int i = 0; i < 16; i++) { \
    vec x = vec_load_le(in + (i*vecsize)); \
    vec_store_le(out + (i*vecsize),vec_xor(x,st[i]));}

#define sum_states16(a,b) \
  for (int i = 0; i < 16; i++) (a)[i] = vec_add((a)[i],(b)[i])

#define copy_state16(a,b) \
  for (int i = 0; i < 16; i++) (a)[i] = (b)[i]

#define xor_bytes(a,b,c,l) \
  for (int i = 0; i < (l); i++) (a)[i] = (b)[i] ^ (c)[i]

#endif
