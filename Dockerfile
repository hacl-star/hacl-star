FROM ubuntu:bionic

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>
# Based on the original F* formula with Daniel Fabian

# Define versions of dependencies
ENV opamv 4.05.0
ENV z3v 4.5.1.1f29cebd4df6-x64-ubuntu-14.04
ENV fstarv stable
ENV kremlinv master

# Install required packages and set versions
RUN apt-get -qq update
RUN apt-get install --yes sudo wget libssl-dev libsqlite3-dev g++ gcc m4 make opam pkg-config python libgmp3-dev unzip cmake

# Create user
RUN useradd -ms /bin/bash Work
RUN echo "Work ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER Work
WORKDIR /home/Work

# Prepare build (OCaml packages)
ENV OPAMYES true
RUN opam init
RUN echo ". /home/Work/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true" >> .bashrc
RUN opam switch ${opamv}
RUN opam install ocamlfind batteries sqlite3 fileutils yojson ppx_deriving_yojson zarith pprint menhir ulex process fix wasm stdint

# Prepare and build Z3
RUN wget https://github.com/FStarLang/binaries/raw/master/z3-tested/z3-${z3v}.zip
RUN unzip z3-${z3v}.zip
RUN mv z3-${z3v} z3
ENV PATH "/home/Work/z3/bin:$PATH"
WORKDIR /home/Work

# Prepare and build F*
ARG RESET_FSTAR=0
RUN git clone https://github.com/FStarLang/FStar.git
WORKDIR /home/Work/FStar
RUN git checkout ${fstarv}
ENV PATH "~/FStar/bin:$PATH"
RUN opam config exec -- make -C src/ocaml-output -j
RUN opam config exec -- make -C ulib/ml
WORKDIR /home/Work

# Prepare and build KreMLin
ARG RESET_KREMLIN=0
RUN git clone https://github.com/FStarLang/kremlin.git
WORKDIR /home/Work/kremlin
RUN git checkout ${kremlinv}
ENV PATH "~/kremlin:$PATH"
RUN opam config exec -- make
WORKDIR /home/Work

# Prepare and build HACL*
ARG RESET_HACL=0
RUN git clone https://github.com/mitls/hacl-star.git
WORKDIR /home/Work/hacl-star
RUN git checkout master
ENV FSTAR_HOME /home/Work/FStar
ENV KREMLIN_HOME /home/Work/kremlin
RUN opam config exec -- make snapshots/hacl-c -j
RUN opam config exec -- make build
WORKDIR /home/Work
