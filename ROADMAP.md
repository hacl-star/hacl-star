# ROADMAP

Hacl\* provides two different kinds of APIs:

* C APIs, extracted from verified Hacl\* source code. These APIs provide safety correctness, and side-channel resistance guarantees. 
They include verified, drop-in replacement for e.g. NaCl and libsodium.

* F\* APIs, with precise type annotations that formalize these guarantees, and 
with additional verified security guarantees based on standard cryptographic assumptions. 
These APIs are used to build and verify larger secure functionalities, such as miTLS.

## Verified Crypto Code: Functional Correctness, Runtime Safety, and Side-Channel Resistance

## Secure APIs: Idealization, Agility, and Multiplexing

The F\* APIs are more general and complex than the C APIs. 

They feature *idealized variants*, reflecting standard
cryptographic notions of security. These variants are used in
type-based security proofs, for instance to define the intermediate
games in cryptographic reductions. They are verified then discarded by
the F\* compiler. They are never extracted to C.

They often feature *cryptographic agility*, meaning here that a given
functionality (say `Hash`) is parameterize by a choice between
different algorithms that realize it (say `SHA1`, `SHA256`, and
`SHA384`).

They also feature *implementation multiplexing*, meaning that each
algorithm may be implemented by different cryptographic providers (say
Hacl\*, Vale, and OpenSSL).

NB: third-party providers such as OpenSSL are unverified. They
are included for convenience (e.g. for interoperability and
performance testing) and for completeness (for algorithms used in
miTLS but not currently coded in Hacl*). As explained below, they are
optional: Hacl\* can be configured to exclude them from the TCB at
compile-time.

# Project Structure and Internal Dependencies

`spec` includes pure functional definitions for our cryptographic
algorithms, such as `Poly1305.Spec.fst`. These simple definitions are
executable in F* for basic testing (with terrible performance). They
are used as the high-level, mathematical specification for verifying
our low-level imperative code. After verification, the compiler
erases them, so they are never extracted to C.
`spec' also includes interfaces for these algorithms, such as
`Poly1305.fsti` that further specify the imperative calling convention
and stateful pre- and post-conditions for our code.

`code` includes Hacl\* code, such as `Poly1305.fst` verified against
their specifications and interfaces, as well as auxiliary files for
their implementation and their proofs, such as `Poly1305.Lemmas.fst`.
`code` depends only on `spec`. It has subdirectories for different
kinds of algorithms, such as `code/poly1305` and `code/salsa-family`.

`code/experimental` includes additional Hacl\* code, not necessarily verified. 

`other_providers` include third-party cryptographic providers and some
adapter code. It is used by both `secureAPI` and `test`.

`secureAPI` includes F\* code supporting our cryptographic security model and proofs. It implements our F\* APIs. It depends on `spec` and (indirectly) `code` and `other_providers`.

`snapshots` provides C code compiled and extracted from `code`, thereby implementing our C APIs.

`test` includes various tests, against the interfaces of `spec`.

`apps` provides sample applications built on top of our C API, such as `pneutube`.

# TODO 

unclear where are the flags and the provider configurations: in `secureAPI` or in `spec` ? 

rename from crypto_proofs; explain it is more general than miTLS. 

rename many files there...

add pointer to IACR

# Filename conventions (from slack discussion summary)


We intend to use the HACL project as the only crypto provider for miTLS, with functional correctness, crypto soundness, and multiplexing with other implementations such as Spartan and OpenSSL. At the same time, we still want to be able to compile HACL's API without any 3rd party implementation and/or without full functional correctness and crypto soundness.

We need to agree on naming conventions for many files. As a concrete example, for AES256 we may have .fst (and sometimes .fsti) as follows:

- `AES.Spec` for pure functional specifications and shared declarations for all implementations
- `AES.Hacl`, `AES.Hacl64`,`AES.Spartan`, `AES.OpenSSL` for the supported implementations, proved (or assumed) functionally correct wrt `AES.Spec`
- `AES.Hacl.Lemmas` etc for auxiliary proof of functional correctness
- `AES` for the main, abstract API, multiplexing between these implementations (and possibly between algorithms, e.g. for agile functionalities)
- `AES.PRF`, `AES.SPRF` for its conditional idealizations, assuming AES is a PRF, or a super PRF
- `AES.PRF.Lemmas` etc fro auxiliary proofs of computational soundness.

where in fact `AES` stands e.g. for `Crypto.Symmetric.AES`

We are not sure how to split files between directories... It is not essential since we systematically use qualified module names. One approach is to put e.g. all AES files (or symmetric ciphers) into a directory. Another to have separate toplevel directories {spec,sound,hacl,openSSL,spartan,test} with ad hoc subdirectories.

As proposed by Jonathan, we plan to support flexible configuration by having `AES` multiplex between configurations, e.g.

```
module AES (...)

let encrypt i k input output =
  match aes_provider i with
  | Hacl    -> AES.Hacl.encrypt    i k input output
  | Spartan -> AES.Spartan.encrypt i k input output
  | OpenSSL -> AES.OpenSSL.encrypt i k input output
```
and we can statically select e.g. only the HACL code provided that

- we compile AES with the `--partial` flag
- we define with `let aes_provider i = Hacl`
- we have interfaces `AES.Spartan.fsti` and `AES.OpenSSL.fsti` (but not their implementations)

# Some other meeting notes on hacl-star (restructure branch)

- code: thematic dirs (with functional correctness) + experimental for 2nd tier + lib (wrapping fstar; needed maybe for integers)

- doc/tutorial (from hacs) including vale for now.

- snapshots (aka branches from prior papers) and extracted, tweaked, persisted C code. Includes some testing. Direct access to C code for people who don't care about fstar.

- next to each implementation code, there may be a pure low-level spec.

