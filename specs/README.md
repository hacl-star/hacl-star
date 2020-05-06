# HACL* specifications

This directory contains F* formal specifications against which the
code of HACL*, Vale, and EverCrypt are verified.

These specifications have been written with a view towards
succinctness and readability, and we encourage others to carefully
review them, since they constitute an important part of our trusted
computing base (TCB).

All our specifications are written in the Pure fragment of F* and rely
only on F* builtins and the HACL* libraries in `/lib`.  Each
specification is typechecked using F* and tested against standard
test vectors by compilation to OCaml. (See the included
`Makefile` for details.)
