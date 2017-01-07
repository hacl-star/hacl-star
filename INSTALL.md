# INSTALLATION

Hacl* relies on [F*](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin) for verification.

Both repositories are included as submodules which you can initialize running `git submodule update --init`.

### Installing F*

Installation instructions for F* can be found [here](https://github.com/FStarLang/FStar/blob/master/INSTALL.md#prerequisite-for-steps-2-and-3-working-ocaml-setup). F* is quickly evolving and it is unlikely that the binary packages will be up-to-date, so we recommand building the tool from the OCaml snapshot.

Wherever you install F*, you should export the `FSTAR_HOME` variable to its root directory.

### Installing KreMLin

KreMLin relies on F* so please make sure that you have a running F* binary.
Then KreMLin specific instructions are to be found [there](https://github.com/FStarLang/kremlin/blob/master/README.md).

### Verifying / extracting the code

To verify and extract the code *Makefiles* are present in the [code](code) directory, and its sub directories.
Run `make verify` to run the verification targets, or `make extract-c` to compile to F* code to c.

### C code

Already extracted C code can be found in the [extracted/c](extracted/c) directory.
