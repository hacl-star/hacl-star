# INSTALLATION

If you only are interested in the latest version of the generated C code,
or Web Assembly code, installing the toolchain is not required.
In that scenario, only a recent C compiler and CMake are needed for building libraries.

The latest version of the verified C code is available
in [snapshots/hacl-c](snapshots/hacl-c).

The latest version of the Web Assembly code is available
in [snapshots/hacl-c-wasm](snapshots/hacl-c-wasm).

HACL* relies on [F*](https://github.com/FStarLang/FStar) (`stable` branch) and
[KreMLin](https://github.com/FStarLang/kremlin) (`master` branch) for verification,
extraction to OCaml (`specs/`) and extraction to C (`code/`).

### Installing dependencies and the toolchain

In the case where you do want to perform F* verification and extraction
installing some prerequisites is needed.

0. A Docker image is available, in the root directory, to build the toolchain if you want.

1. Otherwise, there are few dependencies that must be manually installed on your
machine before being able to verify or extract HACL* using the toolchain:
- OPAM
- CMake (if building libraries from C code)
- Emscripten (if generating the Web Assembly library from C code)

Please do not miss the `opam init` and ``` eval `opam config env` ``` steps.

2. Installing the toolchain (FStar, OCaml, KreMLin and Z3) can be achieved
easily by running `make prepare` from within the HACL* root directory.

#### Alternative setup

In case where `make prepare` fails on your machine,
Everest allows a reasonably easy setup with most up-to-date stable
combination of OPAM, F*, KreMLin, Z3.
```
git clone -b stable https://github.com/project-everest/everest.git
cd everest
./everest check
./everest FStar pull make
./everest kremlin pull make
```

### Installing HACL*

To start using HACL* you can simply download the stable or master
branch of the repository and setting the following environnement variable.

```
export HACL_HOME= <path-to hacl-star>
```

Calling `make` from the root directory will give you more information.


### HACL* master

The HACL* repository has multiple branches: `stable`, `master` and
feature branches. The main production branch is `master`; as it
is under Continuous Integration for verification and code generation
it should be working at all times. We maintain an old version of
HACL* in the `stable` branch, but we do not recommand using it.
