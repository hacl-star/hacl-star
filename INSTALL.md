# INSTALLATION
 
Hacl* relies on [F*](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin) for verification.
The submodules are automatically installed when running the makefile targets.

### Environment

Please set FSTAR_HOME and KREMLIN_HOME in your environnement variables:
```
export FSTAR_HOME= <path-to hacl-star/dependencies/FStar>
export KREMLIN_HOME= <path-to hacl-star/dependencies/kremlin>
```

### Installing FStar and KreMLin

The only prerequisite to install F* and KreMLin is OCaml.
Please install the OCaml compiler and the OPAM package manager.

Then, from the Hacl* root repository:
```
make prepare
```

This will install required OPAM packages and build F* and Kremlin.

To generate the library, run:
```
make
```

### Verifying / extracting the code

To verify and extract the code *Makefiles* are present in the [code](code) directory, and its sub directories.
Run `make verify` to run the verification targets, or `make extract-c` to compile to F* code to c.

### C code

Already extracted C code can be found in the [snapshots/hacl-c](snapshots/hacl-c) directory.
