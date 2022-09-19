module Vale.Def.Sel

open FStar.UInt
open FStar.Seq
open FStar.BV
open FStar.BitVector
open Vale.Def.Words_s

let sel (a b c:bool) : bool = if c then a else b

let rec logsel_vec (#n: pos) (a b c: bv_t n) : Tot (bv_t n) =
  if n = 1
  then create 1 (sel (index a 0) (index b 0) (index c 0))
  else append (create 1 (sel (index a 0) (index b 0) (index c 0))) (logsel_vec #(n - 1) (slice a 1 n) (slice b 1 n) (slice c 1 n))

#push-options "--initial_fuel 1 --max_fuel 1"
let rec logsel_vec_definition (#n: pos) (a b c: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logsel_vec #n a b c) i = sel (index a i) (index b i) (index c i))
      [SMTPat (index (logsel_vec #n a b c) i)] =
  if i = 0 then () else logsel_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (slice c 1 n) (i - 1)
#pop-options

let logsel (#n:pos) (a:uint_t n) (b:uint_t n) (c:uint_t n) : Tot (uint_t n) =
  from_vec #n (logsel_vec #n (to_vec #n a) (to_vec #n b) (to_vec #n c))

unfold let isel32 (a:nat32) (b:nat32) (c:nat32) : nat32 = logsel #32 a b c
