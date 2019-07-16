--------------------------------------------------------------------

Some notes on the HACL* naming conventions... :)

--------------------------------------------------------------------

--------------------------------------------------------------------


Tabs are two spaces !

Endline must be trimmed from whitespaces !


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

For maximum bounds, max is inclusive and names should be

```
inline_for_extraction
let max_blah: size_nat = 42
```
such that signatures can use it as preconditions as

```
val f: n:size_nat{n <= max_blah} -> Tot size_nat
```

--------------------------------------------------------------------

Prefer this kind of style for signatures:

```


#set-options "--z3rlimit 50"


val blake2b:
    nn:size_t{1 <= v nn /\ v nn <= 64}
  -> output:lbuffer uint8 nn
  -> ll:size_t
  -> d:lbuffer uint8 ll
  -> kk:size_t{v kk <= 64 /\ (if v kk = 0 then v ll < pow2 128 else v ll + 128 < pow2 128)}
  -> k:lbuffer uint8 kk ->
  Stack unit
  (requires fun h ->
    live h output /\ live h d /\ live h k /\
    disjoint output d /\ disjoint output k)
  (ensures  fun h0 _ h1 ->
    modifies1 output h0 h1 /\
    h1.[|output|] == Spec.Blake2.blake2b h0.[|d|] (v kk) h0.[|k|] (v nn))

let blake2b nn output ll d kk k =

```

We enforce two empty lines on top of the pragmas and val signatures.
The same applies to an annotated let with no val.

There must be an empty line between the val and the let.

The arrow in val signatures are at the beginning of the line.
The arrow preceding the effect is on the same line as the last
argument.

There is no space between the name and the types in the val or
annotated let.

There are no parenthesis between the requires/ensures clauses and the
Lambda.

Predicates start on the line below the lambda.

Logical connectors are at the end of the lines.

--------------------------------------------------------------------

Prefer anotating the effect with `Tot`, this provides a more visible
delimitation between the parameters and the return type of the
functions than the `:`

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
--------------------------------------------------------------------
--------------------------------------------------------------------
--------------------------------------------------------------------
--------------------------------------------------------------------




--------------------------------------------------------------------

Recommanded but not mandatory guidelines

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
