--------------------------------------------------------------------

Some notes on the HACL* naming conventions... :)

--------------------------------------------------------------------

Define types with suffixes that provide information on what it inside:

In protocols such as Signal, MLS or Wireguard we use the following
conventions to name types:

```
type key_public_s = ...
```

The idea is that `_s` allows to know that this is a sequence (Seq.seq)

Some default conventions that we are using:

`_n` Mathematical integers
`_t` Machine integers
`_s` Pure sequences
`_p` LowStar buffers
`_l` Pure Lists
`_c` Sum types
`_i` Inductives
`_r` record
`_a` Abstract
`_x` Tuples

This allows to define `key_public_s` in a Pure specification and
`key_public_p` in the equivalent LowStar code.

--------------------------------------------------------------------

Prefer anotating the effect with `Tot`, this provides better
delimitation between the parameters and the return type of the
functions that the `:`

--------------------------------------------------------------------

In algorithms and protocol stacks, sizes should be preferably defined
as `size_key` or `size_nonce` and NOT `key_len` or `key_bytes` (so that
we can use those as variable names).

```
inline_for_extraction
let size_key (a:algorithm) : Tot size_nat =
  match a with
  | AEAD_AES128_GCM -> 16
  | AEAD_Chacha20_Poly1305 -> 32
```

--------------------------------------------------------------------

In an agile setting a module should use the type `algorithm` eg.

```
type algorithm =
  | ALG1
  | ALG2
```
so that we can build things like the HPKE ciphersuite

`type ciphersuite = Hash.algorithm & DH.algorithm & AEAD.algorithm`

--------------------------------------------------------------------

Prefer this kind of style for signatures:

```
val encap:
    cs: ciphersuite
  -> e: entropy
  -> pk: key_public_s cs
  -> context: lbytes 32 ->
  Tot (entropy & (option (key_s cs & key_public_s cs)))
```

The arrow and the effects allow easy distinctions between the
arguments and the return type.
