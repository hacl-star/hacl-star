####  Makefile for compilation on Linux  ####

FRODO_HOME = ../../../..
KREMLIN_HOME ?= ../../../../../../kremlin

USE_OPENSSL ?= FALSE
GENERATION_A ?= CSHAKE128

CC?=gcc
ifeq "$(CC)" "gcc"
    COMPILER=gcc
else ifeq "$(CC)" "clang"
    COMPILER=clang
endif

ARCHITECTURE=_AMD64_
USE_OPT_LEVEL=_OPTIMIZED_FAST_

ifeq "$(GENERATION_A)" "AES128"
    USE_GENERATION_A=_AES128_FOR_A_
else ifeq "$(GENERATION_A)" "CSHAKE128"
    USE_GENERATION_A=_CSHAKE128_FOR_A_
else
    USE_GENERATION_A=_AES128_FOR_A_
endif

USING_OPENSSL=_USE_OPENSSL_
ifeq "$(USE_OPENSSL)" "FALSE"
    USING_OPENSSL=NO_OPENSSL
endif

OPENSSL_INCLUDE_DIR=/usr/include
OPENSSL_LIB_DIR=/usr/lib

AR=ar rcs
RANLIB=ranlib
LN=ln -s

CFLAGS= -O3 -std=gnu11 -Wall -Wextra -march=native -DLINUX -D$(ARCHITECTURE) -D$(USE_OPT_LEVEL) -D$(USE_GENERATION_A) -D$(USING_OPENSSL)
ifeq "$(USE_OPENSSL)" "FALSE"
LDFLAGS=-lm
else
CFLAGS+= -I$(OPENSSL_INCLUDE_DIR)
LDFLAGS=-lm -L$(OPENSSL_LIB_DIR) -lssl -lcrypto
endif


ifeq "$(ARCHITECTURE)" "_AMD64_"
ifeq "$(USE_OPT_LEVEL)" "_OPTIMIZED_FAST_"
CFLAGS += -mavx2 -maes -msse2
endif
endif

.PHONY: all check clean prettyprint

all: lib976 tests KATS

objs/%.o: %.c
	@mkdir -p $(@D)
	$(CC) -c  $(CFLAGS) $< -o $@

objs/frodo976.o: frodo976.c
	@mkdir -p $(@D)
	$(CC) -c  $(CFLAGS) $< -o $@


# RAND
objs/random/random.o: random/random.h
RAND_OBJS := objs/random/random.o

# KEM_FRODO
KEM_FRODO976_OBJS := $(addprefix objs/, frodo976.o util.o)
KEM_FRODO976_HEADERS := api.h config.h frodo_macrify.h
$(KEM_FRODO976_OBJS): $(KEM_FRODO976_HEADERS)

# AES
AES_OBJS := $(addprefix objs/aes/, aes.o)
AES_HEADERS := $(addprefix aes/, aes.h)
$(AES_OBJS): $(AES_HEADERS)

# SHAKE
SHAKE_OBJS := $(addprefix objs/sha3/, fips202.o)
SHAKE_HEADERS := $(addprefix sha3/, fips202.h)
$(SHAKE_OBJS): $(SHAKE_HEADERS)

ifeq "$(USE_OPT_LEVEL)" "_OPTIMIZED_FAST_"
# AES_NI
AES_NI_OBJS := $(addprefix objs/aes/, aes_ni.o)

ifeq "$(GENERATION_A)" "CSHAKE128"
# SHAKEx4
SHAKEx4_OBJS := $(addprefix objs/sha3/, fips202x4.o keccak4x/KeccakP-1600-times4-SIMD256.o)
SHAKEx4_HEADERS := $(addprefix sha3/, fips202x4.h keccak4x/KeccakP-1600-times4-SnP.h)
$(SHAKEx4_OBJS): $(SHAKEx4_HEADERS)
endif
endif

lib976: $(KEM_FRODO976_OBJS) $(RAND_OBJS) $(AES_OBJS) $(AES_NI_OBJS) $(SHAKE_OBJS) $(SHAKEx4_OBJS)
	rm -rf frodo
	mkdir frodo
	$(AR) frodo/libfrodo.a $^
	$(RANLIB) frodo/libfrodo.a

tests: lib976 tests/ds_benchmark.h
	$(CC) $(CFLAGS) -L./frodo tests/test_KEM976.c -lfrodo $(LDFLAGS) -o frodo/test_KEM

tests-fstar: lib976 tests/ds_benchmark.h
ifeq "$(GENERATION_A)" "CSHAKE128"
	        $(CC) $(CFLAGS) -L$(FRODO_HOME)/code/frodo-c.976-cSHAKE -L$(KREMLIN_HOME)/kremlib/dist/generic tests/test_KEM976.c -lfrodo -lkremlib $(LDFLAGS) -o frodo/test_KEM_fstar $(ARM_SETTING)
else
	        $(CC) $(CFLAGS) -L$(FRODO_HOME)/code/frodo-c.976-AES -L$(KREMLIN_HOME)/kremlib/dist/generic tests/test_KEM976.c -lfrodo -lkremlib $(LDFLAGS) -o frodo/test_KEM_fstar $(ARM_SETTING)
endif

lib976_for_KATs: $(KEM_FRODO976_OBJS) $(AES_OBJS) $(AES_NI_OBJS) $(SHAKE_OBJS) $(SHAKEx4_OBJS)
	$(AR) frodo/libfrodo_for_testing.a $^
	$(RANLIB) frodo/libfrodo_for_testing.a

KATS: lib976_for_KATs
ifeq "$(GENERATION_A)" "CSHAKE128"
	$(CC) $(CFLAGS) -L./frodo tests/PQCtestKAT_kem_cshake.c tests/rng.c -lfrodo_for_testing $(LDFLAGS) -o frodo/PQCtestKAT_kem_cshake
else
	$(CC) $(CFLAGS) -L./frodo tests/PQCtestKAT_kem.c tests/rng.c -lfrodo_for_testing $(LDFLAGS) -o frodo/PQCtestKAT_kem
endif

KATS-fstar:
	mkdir -p frodo
ifeq "$(GENERATION_A)" "CSHAKE128"
	$(CC) $(CFLAGS) -L$(FRODO_HOME)/code/frodo-c.976-cSHAKE -L$(KREMLIN_HOME)/kremlib/dist/generic tests/PQCtestKAT_kem_cshake.c tests/rng.c -lfrodo_for_testing -lkremlib $(LDFLAGS) -o frodo/PQCtestKAT_kem_fstar $(ARM_SETTING)
else
	$(CC) $(CFLAGS) -L$(FRODO_HOME)/code/frodo-c.976-AES -L$(KREMLIN_HOME)/kremlib/dist/generic tests/PQCtestKAT_kem.c tests/rng.c -lfrodo_for_testing -lkremlib $(LDFLAGS) -o frodo/PQCtestKAT_kem_fstar $(ARM_SETTING)
endif

check: tests

clean:
	rm -rf objs *.req frodo
	find . -name .DS_Store -type f -delete

prettyprint:
	astyle --style=java --indent=tab --pad-header --pad-oper --align-pointer=name --align-reference=name --suffix=none *.h */*.h */*.c
