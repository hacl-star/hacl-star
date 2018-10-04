## Implementations of SHA1, SHA2 and MD5 hash algorithms

### What this directory is about

This directory contains a revamped implementation of several hash algorithms. In
particular, this code demonstrates:
- the use of the latest F\* features, e.g. top-level immutable arrays
- guidelines for multiplexing and code organization.

In this directory, and more generally on the HACL\* side of things, we are
concerned with:

- static multiplexing, i.e. functions that *do not* extract, but perform static
  dispatch on a finite set of cases; the typical example is:

  ```
  inline_for_extraction noextract
  let update (a: hash_alg) (s: state a) (b: bytes { B.length b % block_size a = 0 }) =
    match a with
    | SHA2_256 -> update_sha2_256 s b
    | SHA2_512 -> update_sha2_512 s b
  ```

  the `update` function cannot extract to C, because `state a` is either
  `uint32_t *` or `uint64_t *`; however, any caller is welcome to call `update`
  as long as they apply it to a constant first argument, triggering partial
  evaluation by F\*

- HACL-only implementations; we do not talk about Vale; in the rare event that
  HACL\* should need some generic functionality (e.g. PRNG), HACL\* will use
  EverCrypt.

- single-algorithm specialized modules, i.e. `Hacl.Hash.SHA2`, which contains
  monomorphic, specialized versions of all the generic hash combinators

We are not concerned with:

- dynamic multiplexing, which involves run-time tests and a uniform
  representation of state, in C, for all algorithms

- other implementations, e.g. Vale.

These concerns belong in EverCrypt.

### Code structure

Tentative.

- `Hacl.Hash.Definitions`, Low\* types for states, data structures and stateful
  functions, along with helper functions defined for all hash algorithms (e.g.
  block size, etc.)
- `Hacl.Hash.PadFinish`, generic implementations of `pad` and `finish` for all
  hash algorithms
- `Hacl.Hash.X.Core`, base functions for algorithm `X`, i.e. `alloca`, `init`,
  `update`, `pad` and `finish`
- `Hacl.Hash.Agile`, a layer of static multiplexing for base functions across
  all hash algorithms
- `Hacl.Hash.MerkleDamgard`, the generic construction built on top of static
  multiplexing, using non-extractable higher-order functions, i.e.
  `mk_update_multi`, `mk_update_last`, `mk_hash`
- `Hacl.Hash.X`, a full set of functions for algorithm `X`, including all the
  base functions along with specialized, monomorphic instances of the generic
  constructions above
