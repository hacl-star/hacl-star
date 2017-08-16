FROM ubuntu:xenial

MAINTAINER Benjamin Beurdouche <benjamin.beurdouche@inria.fr>
# Based on the original F* formula with Daniel Fabian

# Define versions of dependencies
ENV opamv 4.04.2
ENV z3v 4.5.1.1f29cebd4df6-x64-ubuntu-14.04
ENV fstarv 787a4fb921ea2ceee65396bb8c6276d3de99a94e
ENV kremlinv 32c177d6622badce550aa08c1158f8b824480531

# Install required packages and set versions
RUN apt-get -qq update
RUN apt-get install --yes sudo wget libssl-dev libsqlite3-dev g++-5 gcc-5 m4 make opam pkg-config python libgmp3-dev unzip
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-5 200
RUN update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-5 200

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

# Prepare and build HaCl*
RUN git clone https://github.com/mitls/hacl-star.git
WORKDIR /home/Work/hacl-star
RUN git checkout production-nss
ENV FSTAR_HOME /home/Work/hacl-star/dependencies/FStar
ENV KREMLIN_HOME /home/Work/hacl-star/dependencies/kremlin
RUN opam config exec -- make
WORKDIR /home/Work