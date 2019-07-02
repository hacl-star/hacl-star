FROM ubuntu:18.04

RUN apt-get -qq update
RUN apt-get install -y software-properties-common
RUN add-apt-repository -y ppa:avsm/ppa # for opam 2
RUN apt-get -qq update
RUN apt-get install -y sudo wget libssl-dev libsqlite3-dev g++ gcc m4 make opam pkg-config python libgmp3-dev unzip cmake

RUN useradd -ms /bin/bash build
RUN echo "build ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER build
WORKDIR /home/build

RUN opam init -y --disable-sandboxing --compiler=4.07.0
RUN opam update
RUN opam install -y ocamlbuild ocamlfind batteries stdint zarith yojson fileutils pprint menhir ulex ppx_deriving ppx_deriving_yojson process pprint visitors fix wasm

ARG fstar=d95e3c4
ARG kremlin=ba36259
ARG hacl=2a76a4a

ENV z3=z3-4.8.5-x64-debian-8.11
ADD https://github.com/FStarLang/binaries/raw/master/z3-tested/${z3}.zip .
RUN sudo unzip ${z3}.zip
ENV PATH=/home/build/${z3}/bin:${PATH}

RUN git clone https://github.com/FStarLang/FStar.git
ENV FSTAR_HOME=/home/build/FStar
WORKDIR $FSTAR_HOME
RUN git checkout ${fstar}
RUN opam config exec -- make
WORKDIR /home/build

RUN git clone https://github.com/FStarLang/kremlin.git
ENV KREMLIN_HOME=/home/build/kremlin
WORKDIR $KREMLIN_HOME
RUN git checkout ${kremlin}
RUN opam config exec -- make
WORKDIR /home/build

RUN rm -rf hacl-star
RUN git clone https://github.com/project-everest/hacl-star.git
ENV HACL_HOME=/home/build/hacl-star
WORKDIR $HACL_HOME
RUN git checkout ${hacl}
RUN find . -name "*[ti].hints" -delete
RUN opam config exec -- make -C specs -i
RUN opam config exec -- make -C code snapshot -i
RUN opam config exec -- make -C code snapshot
RUN opam config exec -- make -C code test-snapshot
WORKDIR /home/build
