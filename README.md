hacl-star
=========
[![Build Status](https://travis-ci.org/mitls/hacl-star.svg?branch=master)](https://travis-ci.org/mitls/hacl-star)

A formally verified cryptographic library in F*

# Code test targets (WIP)

Run `make -C test` to run the extraction tests currently available (to OCaml, C extraction to appear soon).


# Code verification targets (WIP)

Run `make -C crypto_hst` to run the verification.
NB: this code relies on the F* low-level memory model (see [the fstar library](https://github.com/FStarLang/FStar/tree/master/ulib) for more details, in particular `FStar.HyperStack`, `FStar.HST` and `FStar.Buffer`).
