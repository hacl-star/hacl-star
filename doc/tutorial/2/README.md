### Example 2 - Overflow prevention

### Wrapping vs non-overflowing semantics

In previous examples, we were using addition with *wrapping* semantics.
Indeed, `+%^` is some ugly syntactic sugar for the wrapping addition on 64bit unsigned integers in F*:
```F#
val add_mod: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c -> (v a + v b) % pow2 n = v c))
 ```
This pure function guaranties that the result `c` contains a value `v c` that is equal to the sum of the values of `a` and `b`, modulo 2^n where `n` is the number of bits of the integers (64 here).

F* offers two alternatives:
```F#
val add: a:t -> b:t -> Pure t
  (requires (size (v a + v b) n)) // size x n <==> 0 <= x < 2^n
  (ensures (fun c -> v a + v b = v c))

val add_underspec: a:t -> b:t -> Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))
```
The `add` function requires that the some of the arguments cannot overflow. Typechecking will fail if F* cannot prove before hand that the sum of the arguments will not overflow.
The `add_underspec` function can be called with any arguments, but its result is only specified if there was not overflow.

Here we want to implement `fsum` as a bignum addition function, without carries (for now). Hence we do not want any of the limb to limb additions to overflow.

Using the `add` (or `+^` as infix operator) is the best solution to enforce it.

### Constant-time cryptographic algorithms

Cryptographic primitives such as Curve25519 have been chosen for their curve characteristics as well as their particular prime structure.
The modular arithmetic in Z/(2^255-19)Z can be implemented using 4 limbs of 64bits. But then there is not much space left, slightly more than 1 bit, which implies a potential need for carries when implementing the addition on two such values for instance.
In a constant-time setting, the carry would have to be performed every time, which is inefficient. A solution is to represent the integers on more limbs, and thus keeping some space left.
For instance a 255bits integers can be represented by 5 64bit limbs containing a value smaller than 2^51.
Although less memory-efficient, it allows to delay the carries and more efficient constant time coding.
