# HACL* specifications

This directory contains F* specification files for the HACL*
library. Those files are the *truth*: the C code extracted from HACL*
is proven to be functionally equivalent to those F* specifications.

We carefully wrote and reviewed those specifications. We encourage
external reviewers to read and provide us feedback on those
specifications.

These specifications have also been extracted to OCaml code and
unit-tested for more safety.

## Pure F* specifications

HACL* specifications are design with external reviews in mind. We use
a minimal subset of F* types and constructs:

- F* integers (`int`, `nat`, etc.) which are unbounded mathematical
  integers, used to represent bignums for instance.
- F* machine words (`UInt8.t`, `UInt32.t`, etc), unsigned machine
  words with usual operators. NB: to differentiate F* integers
  operators from F* word operators, the later are post-fixed by the
  `^` symbol, e.g. `+^` or `&^`.
- F* sequences (`Seq.seq`), immutable arrays of values. Sequences are
  be created (`create len init`), read at a specific index (`index s
  i` or `s.[i]`), updated at a specific index (`upd s i v` or `s.[i]
  <- v`), sliced (`slice`) or concatenated (`append` or `@`)
- Data-constructors, similar to C structs, super-type composed of
  several fields. E.g. `type point = | Point: x:int -> y:int -> point`.
- F* tuples, a specialized data-constructor binding two fields, `fst`
  and `snd` together.

Other notation details:

- a F* function can be annotated with an *effect* before its returned type. Here this is always `Tot`, which means that the function is *pure* (no side-effects), and terminating.
- `let ( + ) = ...` redefines the `+` infix operation.
- the backticks can be use to use a function as infix. E.g. ``x `add` y``.
- `let rec` denotes recursion.

## Verifying the specifications

To run F* typechecking (verification) on the specifications run `make all-ver`.

NB: the target supports parallelism (add `-j<n>` to the `make` invocation to run `n` simultaneous jobs).

## Running the specifications

To compile the specifications to OCaml code and test them run `make`.

NB: the F* mathematical integers are compiled to OCaml (ZArith) bignums and the sequences are compiled to heavy OCaml constructs. Furthermore, the specifications are designed for RFC compliance and readability, not performance. Therefore, some algorithms (such as SHA2, Ed25519) will perform very poorly.
