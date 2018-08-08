module Words.Two

let lemma_fundamental_div_mod (x:nat64) :
  Lemma (x = x % pow2_32 + pow2_32 * ((x / pow2_32) % pow2_32))
  =
  ()

let nat_to_two_to_nat (n1 n2:nat32) : Lemma
  (nat_to_two 32 (two_to_nat 32 (Mktwo n1 n2)) == Mktwo n1 n2)
  =
  let n = n1 + n2 * pow2_32 in
  assert_norm (two_to_nat 32 (Mktwo n1 n2) == int_to_natN pow2_64 n);
  assert (0 <= n);
  assert (n < pow2_64);
  assert (two_to_nat 32 (Mktwo n1 n2) == n);
  assert_norm (pow2_norm 32 == pow2_32);
  //assert_norm (pow2_norm (2 * 32) == pow2_64);
  assert_norm (nat_to_two 32 n == Mktwo (n % pow2_32) ((n / pow2_32) % pow2_32));
  lemma_fundamental_div_mod n;
  ()
