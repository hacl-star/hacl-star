# ROADMAP

Hacl\* provides two kinds of APIs:

* Verified APIs extracted from Hacl\* source code. 
These APIs provide runtime safety, functional correctness, and side-channel resistance guarantees. 

* Secure APIs, with additional guarantees based on standard cryptographic assumptions. 
These APIs are used to build and verify larger secure functionalities, such as miTLS.

All APIs can be called from F\* (with precise type annotations that capture their verified properties) or directly from C. 
They include verified, drop-in replacement for e.g. NaCl and libsodium.

## Verified Cryptographic Code: Functional Correctness, Runtime Safety, and Side-Channel Resistance

TODO: Summarize guarantees.

## Secure APIs: Idealization, Agility, and Multiplexing

Secure APIs are more general and complex than verified APIs. They feature:

- *conditional idealization*, reflecting standard, computational security assumptions. 
Depending on flags, we switch between real and ideal code. (For example, the ideal code for a hash algorithm
assumed collision-resistant may use a log to detect any hash collision.) 
We use ideal code to define intermediate games in cryptographic reductions and establish stronger properties. 
After verification, ideal code is erased, and only real code is extracted to C.

- *cryptographic agility*, meaning here that a given functionality (say `Hash`) is parameterize by a choice between
different algorithms that realize it (say `SHA1`, `SHA256`, and `SHA384`). This enables the sharing of APIs and proofs.

- *implementation multiplexing*, meaning that each algorithm may be implemented by different cryptographic providers (say
Hacl\*, Vale, and OpenSSL). This is convenient for interoperability and performance testing, 
and also to provide algorithms not yet supported by Hacl*.

Both agility and multiplexing can be resolved at compile-time. 
Thus, Hacl* can be configured to exclude weak algorithms such as SHA1 or unverified providers such as OpenSSL. 

## Project Structure

(Anticipating some suggested renaming)

`spec` includes pure functional definitions for our cryptographic
algorithms, such as `Poly1305.Spec.fst`. These simple definitions are
executable in F* for basic testing (with terrible performance). They
are used as high-level, mathematical specifications for verifying
our lower-level imperative code. After verification, the compiler
erases them, so they are never extracted to C.
`spec` also includes interfaces for these algorithms, such as
`Poly1305.Hacl.fsti` that additionally specify their calling convention
and stateful pre- and post-conditions for our code.

`code` includes Hacl\* cryptographic implementations, verified against
their specifications and interfaces, such as `Poly1305.Hacl.fst`, together with auxiliary files, 
such as `Poly1305.Hacls.Lemmas.fst`.
`code` depends only on `spec`. It has subdirectories for different
kinds of algorithms, such as `code/poly1305` and `code/salsa-family`.

`code/experimental` includes any additional Hacl\* code that has not yet been verified. 

`other_providers` include third-party cryptographic providers and some
adapter F\* code. It implements some of the interfaces of `spec`, and is used by `secureAPI` and `test`.

`secureAPI` includes F\* code supporting our cryptographic security model and proofs. 
It depends on `spec` and (indirectly) `code` and `other_providers`. 

`snapshots` provides C code compiled and extracted from `code`, thereby implementing our C APIs.

`test` includes various tests, against the interfaces of `spec`.

`apps` provides sample applications built on top of our C API, such as `pneutube`.

#### CODING CONVENTIONS

Calls between e.g. different parts of `code` should use `spec` interfaces when present. 

Any idealization, agility, and multiplexing parameters come first, so that they can be resolved by partial application.

Hopefully we can use the same tests for code in `spec`, `secureAPI`, `code`, and `other_providers`.

#### TODO 

Clarify where multiplexing configuration code goes. For example, if we already have `Poly1305.Hacl.fsti` and `Poly1305.OpenSSL.fsti` in `spec`, 
it would be natural to also have `Poly1305.fst` in there. (Conversely, it seems like agility and idealization should live in `secureAPI` for now.)

Within `secureAPI` (aka `crypto_proofs`) clarify where flags and agility configuration go; explain that it is more general than miTLS. Add pointer to IACR

Eventually migrate `coreCrypto` to `other_providers/OpenSSL` (currently providing OpenSSL in F\*) there


#### Filename conventions (from slack discussion summary, adapted a bit)

We intend to use the HACL project as the only crypto provider for miTLS, with functional correctness, crypto soundness, and multiplexing with other implementations such as Spartan and OpenSSL. At the same time, we still want to be able to compile HACL's API without any 3rd party implementation and/or without full functional correctness and crypto soundness.

We need to agree on naming conventions for many files. As a concrete example, for AES256 we may have .fst (and sometimes .fsti) as follows:

- `AES.Spec` for pure functional specifications and shared declarations for all implementations
- `AES.Hacl`, `AES.Hacl64`,`AES.Spartan`, `AES.OpenSSL` for the supported implementations, proved (or assumed) functionally correct wrt `AES.Spec`
- `AES.Hacl.Lemmas` etc for auxiliary proof of functional correctness
- `AES` for the main, abstract API, multiplexing between these implementations (and possibly between algorithms, e.g. for agile functionalities)
- `AES.PRF`, `AES.SPRP` for its conditional idealizations, assuming AES is a PRF, or a super PRP
- `AES.PRF.Lemmas` etc for auxiliary proofs of computational soundness.

where `AES` may actually stand for `Crypto.Symmetric.AES` 

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

