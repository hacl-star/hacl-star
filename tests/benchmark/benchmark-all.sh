#!/bin/bash

OPENSSL=openssl-1.1.1b
PAR=-j20
CONFIGS="gcc-7,g++-7,compact-gcc gcc-8,g++-8,compact-gcc clang-7,clang++-7,compact-gcc clang-8,clang++-8,compact-gcc"
OPENSSL_CONFIGS="openssl-default, openssl-no-asm,no-asm"
SAMPLES=1000

# KREMLIN_INC=$KREMLIN_HOME/include
# KREMLIB_DIR=$KREMLIN_HOME/kremlib/dist
# RFC7748_DIR=$HACL_HOME/tests/rfc7748_src
# EVERCRYPT_DIST=$HACL_HOME/dist/

KREMLIN_INC=~/everest/kremlin-include
KREMLIB_DIR=~/everest/kremlib-dist/generic
RFC7748_DIR=~/everest/rfc7748_src
EVERCRYPT_DIST=~/everest/hacl-dist/

for c in $CONFIGS; do
  IFS=","
  set -- $c
  CC=$1
  CXX=$2
  DIST=$EVERCRYPT_DIST/$3
  unset IFS
  if hash $CC 2>/dev/null && hash $CXX 2>/dev/null; then
    for o in $OPENSSL_CONFIGS; do
      IFS=","
      set -- $o
      OCONF=$1
      OFLAGS=$2
      unset IFS
      if [ ! -d $OCONF-$CC ]; then
        if [ ! -f $OPENSSL.tar.gz ]; then
          wget https://www.openssl.org/source/$OPENSSL.tar.gz --no-check-certificate
        fi
        echo "Building $OCONF-$CC"
        (mkdir -p $OCONF-$CC;
          tar xfz $OPENSSL.tar.gz -C $OCONF-$CC;
          pushd $OCONF-$CC/$OPENSSL;
          CC=$CC CXX=$CXX ./config CFLAGS="-O3 -march=native -mtune=native" $OFLAGS > configure.log 2>&1;
          make $PAR > build.log 2>&1;
          popd > /dev/null)
      fi
      if [ ! -d evercrypt-$OCONF-$CC ]; then
        echo "Configuring evercrypt-$CC with $OCONF-$CC"
        mkdir -p evercrypt-$OCONF-$CC
        (pushd evercrypt-$OCONF-$CC; \
          cmake -DCMAKE_BUILD_TYPE=Release \
            -DCMAKE_C_COMPILER=$CC \
            -DCMAKE_CXX_COMPILER=$CXX \
            -DEVERCRYPT_SRC_DIR=$DIST \
            -DKREMLIN_INC=$KREMLIN_INC \
            -DKREMLIB_DIR=$KREMLIB_DIR \
            -DRFC7748_DIR=$RFC7748_DIR \
            -DUSE_OPENSSL=ON -DOPENSSL_LIB=../$OCONF-$CC/$OPENSSL/libcrypto.a -DOPENSSL_INC=../$OCONF-$CC/$OPENSSL/include \
            .. \
            2>&1; popd > /dev/null) > evercrypt-$OCONF-$CC/configure.log
      fi
      pushd evercrypt-$OCONF-$CC > /dev/null
      echo "(Re-)building evercrypt-$CC using $OCONF-$CC"
      make $PAR >> build.log 2>&1
      echo "Running benchmarks for evercrypt-$CC using $OCONF-$CC"
      (./runbenchmark -n $SAMPLES) >> run.log 2>&1
      popd > /dev/null
    done
  fi
done