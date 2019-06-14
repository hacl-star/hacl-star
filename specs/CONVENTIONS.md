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

Prefer anotating the effect with `Tot`, this provides a more visible
delimitation between the parameters and the return type of the
functions than the `:`

--------------------------------------------------------------------

In algorithms and protocol stacks, sizes should be preferably defined
as `size_key` or `size_nonce` and NOT `key_len` or `key_bytes` (so that
we can use those as variable names).

```
inline_for_extraction
let size_key (a:algorithm) : Tot size_t =
  match a with
  | AEAD_AES128_GCM -> 16ul
  | AEAD_Chacha20_Poly1305 -> 32ul
```

--------------------------------------------------------------------

In many places we use the function `v` to access the mathematical
values under machine integers. Defining constants can be done in
the following style:

```
inline_for_extraction
let vsize_variable: size_nat = 42
```

Typically, in the LowStar code, reusing the spec is trivial:

```
inline_for_extraction
let size_variable: size_t = size vsize_variable // or size 42
```

This in turn allows to be able to call `v` on `size_variable`
such that `v size_variable = vsize_variable`.

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
