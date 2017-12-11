# INSTALLATION

HACL* relies on [F*](https://github.com/FStarLang/FStar) (`stable` branch) and
[KreMLin](https://github.com/FStarLang/kremlin) (`master` branch) for verification,
extraction to OCaml (specs/) and extraction to C (code/).

Everest allows a reasonably easy setup with most up-to-date stable
combination of OPAM, F*, KreMLin, Z3
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

The HACL* repository has multiple branches: stable, master and
feature branches. Feel free to install the cutting edge master.
As it is under continuous integration, it should be working at
all times.
