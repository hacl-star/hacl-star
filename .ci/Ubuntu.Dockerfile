FROM ubuntu:22.04
ENV HOME=/build/
RUN mkdir -p $HOME/hacl-star
COPY . $HOME/hacl-star
WORKDIR $HOME/hacl-star
RUN .ci/ubuntu-setup.sh
RUN .ci/everest-setup.sh
RUN .ci/deps-setup.sh
RUN .ci/verify.sh
