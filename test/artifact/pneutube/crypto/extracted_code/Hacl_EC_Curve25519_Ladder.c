#include "Hacl_EC_Curve25519_Ladder.h"

uint64_t Hacl_EC_Curve25519_Ladder_mk_mask(uint8_t x)
{
  return (uint64_t )0 - (uint64_t )x;
}

uint8_t Hacl_EC_Curve25519_Ladder_nth_bit(uint8_t byte, uint32_t idx)
{
  return byte >> (uint32_t )7 - idx & (uint8_t )1;
}

void
Hacl_EC_Curve25519_Ladder_small_step_exit(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  void *n,
  uint8_t byte,
  void *scalar
)
{
  Hacl_EC_Curve25519_PPoint_copy2(pp, ppq, p, pq);
  return;
}

void
Hacl_EC_Curve25519_Ladder_lemma_helper_0(
  FStar_HyperHeap_rid r,
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem h3
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_lemma_helper_00(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b,
  Hacl_EC_Curve25519_PPoint_point c,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_lemma_helper_02(
  FStar_HyperHeap_rid r,
  Hacl_EC_Curve25519_PPoint_point c,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_lemma_distinct_symm(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_lemma_helper_001(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b,
  Hacl_EC_Curve25519_PPoint_point c,
  Hacl_EC_Curve25519_PPoint_point d,
  Hacl_EC_Curve25519_PPoint_point e,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_small_step_core(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  void *n,
  uint32_t ctr,
  uint8_t b,
  void *scalar
)
{
  uint8_t bit = b >> (uint32_t )7 - ctr & (uint8_t )1;
  uint64_t mask = (uint64_t )0 - (uint64_t )bit;
  Hacl_EC_Curve25519_PPoint_swap_conditional(p, pq, mask);
  Hacl_EC_Curve25519_AddAndDouble_double_and_add(pp, ppq, p, pq, q);
  Hacl_EC_Curve25519_PPoint_swap_conditional(pp, ppq, mask);
  return;
}

void
Hacl_EC_Curve25519_Ladder_small_step(
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  void *n,
  uint32_t ctr,
  uint8_t b,
  void *scalar
)
{
  if ((uint32_t )8 == ctr)
    return;
  else
  {
    Hacl_EC_Curve25519_Ladder_small_step_core(pp,
      ppq,
      p,
      pq,
      q,
      (void *)(void *)(uint8_t )0,
      ctr,
      b,
      (void *)(void *)(uint8_t )0);
    uint8_t bit = b >> (uint32_t )7 - ctr & (uint8_t )1;
    Hacl_EC_Curve25519_PPoint_swap_both(pp, ppq, p, pq);
    Hacl_EC_Curve25519_Ladder_small_step(pp,
      ppq,
      p,
      pq,
      q,
      (void *)(void *)(uint8_t )0,
      ctr + (uint32_t )1,
      b,
      (void *)(void *)(uint8_t )0);
    return;
  }
}

void
Hacl_EC_Curve25519_Ladder_lemma_helper_1(
  FStar_HyperHeap_rid r,
  Prims_prop (*s)(FStar_Heap_aref x0),
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_big_step(
  uint8_t *n,
  Hacl_EC_Curve25519_PPoint_point pp,
  Hacl_EC_Curve25519_PPoint_point ppq,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point pq,
  Hacl_EC_Curve25519_PPoint_point q,
  uint32_t ctr
)
{
  if (Hacl_EC_Curve25519_Parameters_blength == ctr)
    return;
  else
  {
    uint8_t byte = n[Hacl_EC_Curve25519_Parameters_blength - (uint32_t )1 - ctr];
    Hacl_EC_Curve25519_Ladder_small_step(pp,
      ppq,
      p,
      pq,
      q,
      (void *)(void *)(uint8_t )0,
      (uint32_t )0,
      byte,
      (void *)(void *)(uint8_t )0);
    Hacl_EC_Curve25519_Ladder_big_step(n, pp, ppq, p, pq, q, ctr + (uint32_t )1);
    return;
  }
}

void Hacl_EC_Curve25519_Ladder_init_points(Hacl_EC_Curve25519_PPoint_point q, uint64_t *tmp)
{
  uint64_t *p_x = tmp + (uint32_t )34;
  uint64_t *p_y = tmp + (uint32_t )40;
  uint64_t *p_z = tmp + (uint32_t )45;
  uint64_t *inf_x = tmp + (uint32_t )51;
  memcpy(p_x,
    Hacl_EC_Curve25519_PPoint_get_x(q),
    Hacl_EC_Curve25519_Parameters_nlength * sizeof Hacl_EC_Curve25519_PPoint_get_x(q)[0]);
  memcpy(p_y,
    Hacl_EC_Curve25519_PPoint_get_y(q),
    Hacl_EC_Curve25519_Parameters_nlength * sizeof Hacl_EC_Curve25519_PPoint_get_y(q)[0]);
  memcpy(p_z,
    Hacl_EC_Curve25519_PPoint_get_z(q),
    Hacl_EC_Curve25519_Parameters_nlength * sizeof Hacl_EC_Curve25519_PPoint_get_z(q)[0]);
  inf_x[(uint32_t )0] = (uint64_t )1;
}

void
Hacl_EC_Curve25519_Ladder_lemma_helper_2(
  FStar_HyperStack_mem hinit,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  FStar_HyperStack_mem hfin,
  FStar_HyperHeap_rid r
)
{
  return;
}

void
Hacl_EC_Curve25519_Ladder_montgomery_ladder(
  Hacl_EC_Curve25519_PPoint_point res,
  uint8_t *n,
  Hacl_EC_Curve25519_PPoint_point q
)
{
  uint32_t nlp1 = Hacl_EC_Curve25519_Parameters_nlength + (uint32_t )1;
  uint32_t tot_len = (uint32_t )68;
  uint64_t tmp[tot_len];
  memset(tmp, 0, tot_len * sizeof tmp[0]);
  uint64_t *two_p_x = tmp + (uint32_t )0;
  uint64_t *two_p_y = tmp + (uint32_t )6;
  uint64_t *two_p_z = tmp + (uint32_t )11;
  uint64_t *two_p_plus_q_x = tmp + (uint32_t )17;
  uint64_t *two_p_plus_q_y = tmp + (uint32_t )23;
  uint64_t *two_p_plus_q_z = tmp + (uint32_t )28;
  uint64_t *p_x = tmp + (uint32_t )34;
  uint64_t *p_y = tmp + (uint32_t )40;
  uint64_t *p_z = tmp + (uint32_t )45;
  uint64_t *inf_x = tmp + (uint32_t )51;
  uint64_t *inf_y = tmp + (uint32_t )57;
  uint64_t *inf_z = tmp + (uint32_t )62;
  Hacl_EC_Curve25519_PPoint_point
  two_p = Hacl_EC_Curve25519_PPoint_make(two_p_x, two_p_y, two_p_z);
  Hacl_EC_Curve25519_PPoint_point
  two_p_plus_q = Hacl_EC_Curve25519_PPoint_make(two_p_plus_q_x, two_p_plus_q_y, two_p_plus_q_z);
  Hacl_EC_Curve25519_PPoint_point p = Hacl_EC_Curve25519_PPoint_make(p_x, p_y, p_z);
  Hacl_EC_Curve25519_PPoint_point inf = Hacl_EC_Curve25519_PPoint_make(inf_x, inf_y, inf_z);
  Hacl_EC_Curve25519_Ladder_init_points(q, tmp);
  Hacl_EC_Curve25519_Ladder_big_step(n, two_p, two_p_plus_q, inf, p, q, (uint32_t )0);
  Hacl_EC_Curve25519_PPoint_copy(res, two_p);
}

