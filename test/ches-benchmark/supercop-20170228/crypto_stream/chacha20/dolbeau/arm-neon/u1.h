/*
u1.h version $Date: 2014/09/25 12:43:54 $
D. J. Bernstein
Romain Dolbeau
Public domain.
*/

/* helper */
#define vrotlq_u32(a,b) vsliq_n_u32(vshrq_n_u32(a, 32-b),a,b)

  if (!bytes) return;
  while (bytes >=64) {
    uint32x4_t x_0, x_1, x_2, x_3;
    uint32x4_t t_1;

    x_0 = vld1q_u32(x +  0);
    x_1 = vld1q_u32(x +  4);
    x_2 = vld1q_u32(x +  8);
    x_3 = vld1q_u32(x + 12);

    for (i = 0 ; i < ROUNDS ; i += 2) {
      x_0 = vaddq_u32(x_0, x_1);
      x_3 = veorq_u32(x_3, x_0);
      x_3 = vrotlq_u32(x_3, 16);

      x_2 = vaddq_u32(x_2, x_3);
      x_1 = veorq_u32(x_1, x_2);

/*       t_1 = x_1; */
/*       x_1 = vshlq_n_u32(x_1, 12); */
/*       t_1 = vshrq_n_u32(t_1, 20); */
/*       x_1 = veorq_u32(x_1, t_1); */
      x_1 = vrotlq_u32(x_1, 12);

      x_0 = vaddq_u32(x_0, x_1);
      x_3 = veorq_u32(x_3, x_0);
      x_0 = vextq_u32(x_0, x_0, 3);
      x_3 = vrotlq_u32(x_3, 8);

      x_2 = vaddq_u32(x_2, x_3);
      x_3 = vextq_u32(x_3, x_3, 2);
      x_1 = veorq_u32(x_1, x_2);
      x_2 = vextq_u32(x_2, x_2, 1);

/*       t_1 = x_1; */
/*       x_1 = vshlq_n_u32(x_1, 7); */
/*       t_1 = vshrq_n_u32(t_1, 25); */
/*       x_1 = veorq_u32(x_1, t_1); */
      x_1 = vrotlq_u32(x_1, 7);

      x_0 = vaddq_u32(x_0, x_1);
      x_3 = veorq_u32(x_3, x_0);
      x_3 = vrotlq_u32(x_3, 16);

      x_2 = vaddq_u32(x_2, x_3);
      x_1 = veorq_u32(x_1, x_2);

/*       t_1 = x_1; */
/*       x_1 = vshlq_n_u32(x_1, 12); */
/*       t_1 = vshrq_n_u32(t_1, 20); */
/*       x_1 = veorq_u32(x_1, t_1); */
      x_1 = vrotlq_u32(x_1, 12);

      x_0 = vaddq_u32(x_0, x_1);
      x_3 = veorq_u32(x_3, x_0);
      x_0 = vextq_u32(x_0, x_0, 1);
      x_3 = vrotlq_u32(x_3, 8);

      x_2 = vaddq_u32(x_2, x_3);
      x_3 = vextq_u32(x_3, x_3, 2);
      x_1 = veorq_u32(x_1, x_2);
      x_2 = vextq_u32(x_2, x_2, 3);

/*       t_1 = x_1; */
/*       x_1 = vshlq_n_u32(x_1, 7); */
/*       t_1 = vshrq_n_u32(t_1, 25); */
/*       x_1 = veorq_u32(x_1, t_1); */
      x_1 = vrotlq_u32(x_1, 7);
    }
    x_0 = vaddq_u32(x_0, vld1q_u32(x +  0));
    x_1 = vaddq_u32(x_1, vld1q_u32(x +  4));
    x_2 = vaddq_u32(x_2, vld1q_u32(x +  8));
    x_3 = vaddq_u32(x_3, vld1q_u32(x + 12));
    x_0 = veorq_u32(x_0, vld1q_u32((u32*)(m +  0)));
    x_1 = veorq_u32(x_1, vld1q_u32((u32*)(m + 16)));
    x_2 = veorq_u32(x_2, vld1q_u32((u32*)(m + 32)));
    x_3 = veorq_u32(x_3, vld1q_u32((u32*)(m + 48)));
    vst1q_u32((u32*)(out +  0),  x_0);
    vst1q_u32((u32*)(out + 16),  x_1);
    vst1q_u32((u32*)(out + 32),  x_2);
    vst1q_u32((u32*)(out + 48),  x_3);
    
    u32 in12 = x[12];
    u32 in13 = x[13];
    in12 ++;
    if (in12 == 0)
      in13 ++;
    x[12] = in12;
    x[13] = in13;

    bytes -= 64;
    out += 64;
    m += 64;
  }
