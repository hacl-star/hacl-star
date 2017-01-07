# INSTALLATION

Hacl* relies on [F*](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin) for verification.

Both repositories are included as submodules which you can initialize running `git submodule update --init`.

### Environement

Please set FSTAR_HOME in your environnement variables:
`export FSTAR_HOME= <path-to hacl-star/dependencies/FStar>`

Please set KREMLIN_HOME in your environnement variables:
`export KREMLIN_HOME= <path-to hacl-star/dependencies/kremlin>`

### Installing FStar and KreMLin

The only prerequisite to install F* and KreMLin is OCaml.
Please install the OCaml compiler and the OPAM package manager.
If you want to run certain C targets, gcc-6 must be installed.

Then, from the Hacl* root repository:
`make setup`

This will install required OPAM packages and build F* and Kremlin.
You are good to go ! ;)

### Verifying / extracting the code

To verify and extract the code *Makefiles* are present in the [code](code) directory, and its sub directories.
Run `make verify` to run the verification targets, or `make extract-c` to compile to F* code to c.

### C code

Already extracted C code can be found in the [extracted/c](extracted/c) directory.
