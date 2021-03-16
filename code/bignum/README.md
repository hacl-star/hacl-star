# A Verified Implementation of Bignum Library

## Bignum representation

In some sense, we don't provide a *generic* bignum library where the size of bignum is not limited and can be inferred from its value.
In our library, in order to achieve a constant-time implementation, the length of bignum is always limited, for example, with a modulus size.
This means that an array can contain leading zeros and most of the functions will need to access all the elements despite their value.

## Bignum operations

### *Integer arithmetic*
- Hacl.Bignum.fsti <===> Hacl.Spec.Bignum.fsti
  * addition and subtraction: `bn_add1`, `bn_sub1`, `bn_add`, `bn_sub`
  * multiplication and squaring
     * textbook: `bn_mul1`, `bn_mul`, `bn_sqr`
     * karatsuba: `bn_karatsuba_mul`, `bn_karatsuba_sqr`
  * comparison: `bn_eq_mask`, `bn_lt_mask`
  * load and store: `bn_from_uint`, `bn_from_bytes_be[le]`, `bn_to_bytes_be[le]`
  * auxiliary functions: `bn_is_odd`, `cswap2`, `bn_get_ith_bit`, `bn_set_ith_bit` and so on

### *Modular arithmetic*
#### *Montgomery arithmetic*
- Hacl.Bignum.Montgomery.fsti <===> Hacl.Spec.Bignum.Montgomery.fsti
  * Montgomery reduction: `bn_mont_reduction`
  * Montgomery conversion functions: `bn_to_mont`, `bn_from_mont`
  * Montgomery multiplication and squaring: `bn_mont_mul`, `bn_mont_sqr`
  * auxiliary functions: `bn_mont_one`, `bn_check_modulus` and so on

#### *Modular exponentiation* (based on Montgomery arithmetic)
- Hacl.Bignum.Exponentiation.fsti <===> Hacl.Spec.Bignum.Exponentiation.fsti
  * binary method
    * non constant-time impl: `bn_mod_exp_raw` (a right-to-left binary method)
    * constant-time impl: `bn_mod_exp_ct` (Montgomery ladder)
  * fixed-window method
    * non constant-time impl: `bn_mod_exp_fw_raw`
    * constant-time impl: `bn_mod_exp_fw_ct`

 In addition, the **naive** implementation of the following functions is provided:
 #### *Modular reduction*
- Hacl.Bignum.ModReduction.fst <===> Hacl.Spec.Bignum.ModReduction.fst
  * modular reduction based on Montgomery reduction: `bn_mod_slow`
 #### *Modular multiplicative inverse*
- Hacl.Bignum.ModInv.fst <===> Hacl.Spec.Bignum.ModInv.fst
  * modular multiplicative inverse where a modulus is a prime: `bn_mod_inv_prime_raw`

## Functional correctness

The Low* functions (from Hacl.Bignum.\*)  only conform to their low-level spec functions (from Hacl.Spec.Bignum.\*),
i.e. the post-conditions have the form of `as_seq h1 res == S.bn_mul (as_seq h0 a) (as_seq h0 b)` rather than `bn_v h1 res == bn_v h0 a * bn_v h0 b`.
This enforces the user to call the corresponding spec-level lemmas:

- Hacl.Bignum ==> Hacl.Spec.Bignum
- Hacl.Bignum.Montgomery ==> Hacl.Spec.Bignum.Montgomery ==> Hacl.Spec.Montgomery.Lemmas
  * this module is not supposed to get exposed
- Hacl.Bignum.Exponentiation ==> Hacl.Spec.Bignum.Exponentiation ==> Lib.NatMod/Lib.Exponentiation

The reason behind such a design choice may not be obvious if we look only at the Hacl.Bignum module.
This is done in order to simplify the preconditions of the functions and avoid proving the same things twice: in the Low* code and low-level spec.

Also, we don't provide the "safe API" by default, since some of the checks and computations can be eliminated.
For example, FFDHE predefines the group parameters generator `g` and modulus `p`, so we can precompute the constant `r2 = pow2 (nLen + nLen) mod p` and prove that `p` is odd in advance.

To overcome the above, the user can design the "safe API" on the top of "dangerous-to-use" functions,
similar to what was done in the specialized versions of bignum code (see  Hacl.Bignum256 and Hacl.Bignum4096).

## Specialized bignum code

The bignum code can be specialized depending on
- the limb type
  * 32-bit
  * 64-bit
- the number of limbs, i.e. length can be given at
  * run-time (a default implementation)
  * compile time (e.g. Hacl.Bignum256 and Hacl.Bignum4096)
- the aglorithm choices when an instance of the type class is constructed
  * `Hacl.Bignum.bn` <== `Hacl.Bignum.Montgomery.mont` <== `Hacl.Bignum.Exponentiation.exp`
  * For example, `Hacl.Bignum.sqr` can be instantiated with any of these functions:
    * `Hacl.Bignum.bn_mul`
    * `Hacl.Bignum.bn_karatsuba_mul`
    * `Hacl.Bignum.bn_sqr`
    * `Hacl.Bignum.bn_karatsuba_sqr`
    * another custom function as long as its post-condition matches with `Hacl.Bignum.bn_karatsuba_sqr_st`
    * In the `bn_karatsuba_mul` and `bn_karatsuba_sqr` functions, the `bn_mul_threshold` parameter, that denotes the threshold between textbook and karatsuba multiplication, can be also adjusted.
    The parameter highly depends on the cost of multiplication and addition, so it is difficult to make a default choice. Our benchmarks showed that the value 32 seems to be reasonable, i.e. one level of Karatsuba algorithm is performed for 2048-bit numbers.
