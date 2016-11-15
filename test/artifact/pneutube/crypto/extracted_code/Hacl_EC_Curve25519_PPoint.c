#include "Hacl_EC_Curve25519_PPoint.h"

uint64_t *Hacl_EC_Curve25519_PPoint____Point___x(Hacl_EC_Curve25519_PPoint_point projectee)
{
  Hacl_EC_Curve25519_PPoint_point scrut = projectee;
  uint64_t *x = scrut.x00;
  uint64_t *y = scrut.x01;
  uint64_t *z = scrut.x02;
  return x;
}

uint64_t *Hacl_EC_Curve25519_PPoint____Point___y(Hacl_EC_Curve25519_PPoint_point projectee)
{
  Hacl_EC_Curve25519_PPoint_point scrut = projectee;
  uint64_t *x = scrut.x00;
  uint64_t *y = scrut.x01;
  uint64_t *z = scrut.x02;
  return y;
}

uint64_t *Hacl_EC_Curve25519_PPoint____Point___z(Hacl_EC_Curve25519_PPoint_point projectee)
{
  Hacl_EC_Curve25519_PPoint_point scrut = projectee;
  uint64_t *x = scrut.x00;
  uint64_t *y = scrut.x01;
  uint64_t *z = scrut.x02;
  return z;
}

uint64_t *Hacl_EC_Curve25519_PPoint_get_x(Hacl_EC_Curve25519_PPoint_point p)
{
  return Hacl_EC_Curve25519_PPoint____Point___x(p);
}

uint64_t *Hacl_EC_Curve25519_PPoint_get_y(Hacl_EC_Curve25519_PPoint_point p)
{
  return Hacl_EC_Curve25519_PPoint____Point___y(p);
}

uint64_t *Hacl_EC_Curve25519_PPoint_get_z(Hacl_EC_Curve25519_PPoint_point p)
{
  return Hacl_EC_Curve25519_PPoint____Point___z(p);
}

Hacl_EC_Curve25519_PPoint_point
Hacl_EC_Curve25519_PPoint_make(uint64_t *x, uint64_t *y, uint64_t *z)
{
  return (Hacl_EC_Curve25519_PPoint_point ){ .x00 = x, .x01 = y, .x02 = z };
}

Prims_prop
(*Hacl_EC_Curve25519_PPoint_refs(Hacl_EC_Curve25519_PPoint_point p))(FStar_Heap_aref x0)
{
  return (Prims_prop (*)(FStar_Heap_aref x0))(uint8_t )0;
}

void
Hacl_EC_Curve25519_PPoint_swap_conditional_aux_(
  uint64_t *a,
  uint64_t *b,
  uint64_t swap,
  uint32_t ctr
)
{
  if (Hacl_EC_Curve25519_Parameters_nlength == ctr)
    return;
  else
  {
    uint64_t ai = a[ctr];
    uint64_t bi = b[ctr];
    uint64_t y = ai ^ bi;
    uint64_t x = swap & y;
    uint64_t ai_ = x ^ ai;
    uint64_t bi_ = x ^ bi;
    a[ctr] = ai_;
    b[ctr] = bi_;
    Hacl_EC_Curve25519_PPoint_swap_conditional_aux_(a, b, swap, ctr + (uint32_t )1);
    return;
  }
}

void Hacl_EC_Curve25519_PPoint_swap_conditional_aux(uint64_t *a, uint64_t *b, uint64_t swap)
{
  Hacl_EC_Curve25519_PPoint_swap_conditional_aux_(a, b, swap, (uint32_t )0);
  return;
}

FStar_HyperHeap_rid Hacl_EC_Curve25519_PPoint_frame_of(Hacl_EC_Curve25519_PPoint_point p)
{
  return (FStar_HyperHeap_rid )(uint8_t )0;
}

void
Hacl_EC_Curve25519_PPoint_helper_lemma_2(
  FStar_HyperHeap_rid r,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  Prims_prop (*sub)(FStar_Heap_aref x0),
  Prims_prop (*s)(FStar_Heap_aref x0)
)
{
  return;
}

void
Hacl_EC_Curve25519_PPoint_helper_lemma_3(
  FStar_HyperHeap_rid r,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  Prims_prop (*s)(FStar_Heap_aref x0)
)
{
  return;
}

void
Hacl_EC_Curve25519_PPoint_swap_conditional(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b,
  uint64_t is_swap
)
{
  Hacl_EC_Curve25519_PPoint_swap_conditional_aux(Hacl_EC_Curve25519_PPoint_get_x(a),
    Hacl_EC_Curve25519_PPoint_get_x(b),
    is_swap);
  Hacl_EC_Curve25519_PPoint_swap_conditional_aux(Hacl_EC_Curve25519_PPoint_get_y(a),
    Hacl_EC_Curve25519_PPoint_get_y(b),
    is_swap);
  Hacl_EC_Curve25519_PPoint_swap_conditional_aux(Hacl_EC_Curve25519_PPoint_get_z(a),
    Hacl_EC_Curve25519_PPoint_get_z(b),
    is_swap);
  return;
}

void
Hacl_EC_Curve25519_PPoint_copy(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
)
{
  memcpy(Hacl_EC_Curve25519_PPoint_get_x(a),
    Hacl_EC_Curve25519_PPoint_get_x(b),
    Hacl_EC_Curve25519_Parameters_nlength * sizeof Hacl_EC_Curve25519_PPoint_get_x(b)[0]);
  memcpy(Hacl_EC_Curve25519_PPoint_get_y(a),
    Hacl_EC_Curve25519_PPoint_get_y(b),
    Hacl_EC_Curve25519_Parameters_nlength * sizeof Hacl_EC_Curve25519_PPoint_get_y(b)[0]);
  memcpy(Hacl_EC_Curve25519_PPoint_get_z(a),
    Hacl_EC_Curve25519_PPoint_get_z(b),
    Hacl_EC_Curve25519_Parameters_nlength * sizeof Hacl_EC_Curve25519_PPoint_get_z(b)[0]);
}

void
Hacl_EC_Curve25519_PPoint_swap(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
)
{
  Hacl_EC_Curve25519_PPoint_copy(b, a);
  return;
}

void
Hacl_EC_Curve25519_PPoint_helper_lemma_5(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
)
{
  return;
}

void
Hacl_EC_Curve25519_PPoint_swap_both(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b,
  Hacl_EC_Curve25519_PPoint_point c,
  Hacl_EC_Curve25519_PPoint_point d
)
{
  Hacl_EC_Curve25519_PPoint_copy(c, a);
  Hacl_EC_Curve25519_PPoint_copy(d, b);
  return;
}

void
Hacl_EC_Curve25519_PPoint_copy2(
  Hacl_EC_Curve25519_PPoint_point p_,
  Hacl_EC_Curve25519_PPoint_point q_,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point q
)
{
  Hacl_EC_Curve25519_PPoint_copy(p_, p);
  Hacl_EC_Curve25519_PPoint_copy(q_, q);
  return;
}

