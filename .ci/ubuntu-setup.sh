#!/bin/bash

set -e
set -o pipefail

export DEBIAN_FRONTEND=noninteractive
export TZ=America/Los_Angeles

# All of the commands below from the Everest base Docker image.
apt-get --yes update
apt-get install -y wget

# https://docs.microsoft.com/en-us/dotnet/core/install/linux-ubuntu
wget https://packages.microsoft.com/config/ubuntu/22.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
dpkg -i packages-microsoft-prod.deb
rm packages-microsoft-prod.deb
apt-get install -y apt-transport-https
apt-get --yes update

# Here start the Everest-specific packages
until apt-get install --no-install-recommends --yes \
        libssl-dev \
        libsqlite3-dev \
        g++ \
        gcc \
        m4 \
        make \
        opam \
        git \
        pandoc \
        pkg-config \
        libgmp3-dev \
        zip \
        unzip \
        build-essential \
        automake \
        ca-certificates-mono \
        fsharp \
        libunwind8 \
        sudo \
        python2 \
        python3.6 \
        python3-pip \
        python3-setuptools \
        nuget \
        ca-certificates \
        cmake \
        libtool \
        autoconf \
        tzdata \
        openssh-server \
        vim \
        curl \
        wget \
        tcptraceroute \
        emacs \
        libc6 \
        libc6-dev \
        time \
        jq \
        nodejs \
        npm \
        dotnet-sdk-6.0 \
        aspnetcore-runtime-6.0 \
        ; do apt-get --yes update ; done

# Random stuff to make `everest check` happy...

# Install scons
wget https://downloads.sourceforge.net/project/scons/scons/3.0.1/scons-3.0.1.tar.gz
tar xf scons-3.0.1.tar.gz
pushd scons-3.0.1
python3 setup.py install
popd

# Install typescript
npm install -g typescript

# Install less
npm install -g less

# Install madoko
npm install madoko -g && npm install jsdoc -g

# Install node server
npm install http-server -g
