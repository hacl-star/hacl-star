module Vale.Lib.Bv_s
open FStar.Mul
open FStar.UInt
open FStar.BV

// Review: maybe move this to FStar.BV, where the other int2bv_* functions are:
assume val int2bv_uext (#n #m:pos) (x:uint_t n) (y:uint_t (n + m)) : Lemma
  (requires x == y)
  (ensures int2bv #(n + m) y == bv_uext #n #m (int2bv #n x))

