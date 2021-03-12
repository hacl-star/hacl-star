# This is the universal Makefile that will build any distribution of EverCrypt.
# - It is copied from hacl-star/providers/dist/Makefile
# - It relies on the KreMLin-generated Makefile.basic and Makefile.include
#
# This Makefile detects whether OpenSSL and BCrypt are enabled automatically. It
# does so by checking for the presence of EverCrypt_OpenSSL.h and
# EverCrypt_BCrypt.h ; as such, it assumes -bundle EverCrypt.OpenSSL and -bundle
# EverCrypt.BCrypt.
#
# This Makefile may (conservatively) link in some Vale assemblies that may end
# up un-needed in the final shared object.
#
# Additionally, this Makefile works out of the box on Linux, OSX and
# Cygwin/MinGW.
#
# When using OpenSSL, it also expects OPENSSL_HOME to be defined (this is a
# temporary fix for missing algorithms).
#
# The Makefile produces:
# - libevercrypt.so, a shared object where unused symbols have been removed
# - libevercrypt.a

# By default, this Makefile relies on the local checkout of kremlib
KREMLIN_HOME ?= ../kremlin

ifeq (,$(wildcard $(KREMLIN_HOME)/include/kremlib.h))
	$(error Incorrect KREMLIN_HOME)
endif

-include Makefile.config

# 1. The usual pseudo auto-configuration

# TODO: this should all move to the configure script
# TODO: Makefile.config: configure; ./$<
# TODO: include Makefile.config
UNAME		?= $(shell uname)
MARCH		?= $(shell uname -m)
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC
  VARIANT	= -linux
  SO 		= so
else ifeq ($(OS),Windows_NT)
  CFLAGS        += -fno-asynchronous-unwind-tables
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  VARIANT	= -mingw
  SO		= dll
  LDFLAGS	= -Wl,--out-implib,libevercrypt.dll.a
endif

# 2. Parameters we want to compile with, for the generated Makefile

# 3. Honor configurations

# Backwards-compat
ifneq (,$(MLCRYPTO_HOME))
OPENSSL_HOME 	= $(MLCRYPTO_HOME)/openssl
endif

# This is the "auto-detection". Since the parent Makefile runs with -bundle
# EverCrypt.OpenSSL, in case the static configuration doesn't call into
# OpenSSL, then EverCrypt_OpenSSL.h is not generated, meaning if the header
# doesn't exist we are not intend to compile against OpenSSL.
ifneq (,$(wildcard EverCrypt_OpenSSL.h))
  CFLAGS	+= -I $(OPENSSL_HOME)/include
  LDFLAGS 	+= -L$(OPENSSL_HOME) -lcrypto
ifneq ($(OS),Windows_NT)
  LDFLAGS	+= -ldl -lpthread
endif
  SOURCES	+= evercrypt_openssl.c
endif

ifneq (,$(wildcard EverCrypt_BCrypt.h))
  LDFLAGS	+= -lbcrypt
  SOURCES	+= evercrypt_bcrypt.c
endif

OBJS 		+= $(patsubst %.S,%.o,$(wildcard *-$(MARCH)$(VARIANT).S))

include Makefile.basic

CFLAGS		+= -Wno-parentheses -Wno-deprecated-declarations -Wno-\#warnings -Wno-error=cpp -Wno-cpp -g -std=gnu11 -O3

Hacl_Poly1305_128.o Hacl_Streaming_Poly1305_128.o Hacl_Chacha20_Vec128.o Hacl_Chacha20Poly1305_128.o Hacl_Blake2s_128.o Hacl_HMAC_Blake2s_128.o Hacl_HKDF_Blake2s_128.o Hacl_Streaming_Blake2s_128.o: CFLAGS += $(CFLAGS_128)
Hacl_Poly1305_256.o Hacl_Streaming_Poly1305_256.o Hacl_Chacha20_Vec256.o Hacl_Chacha20Poly1305_256.o Hacl_Blake2b_256.o Hacl_HMAC_Blake2b_256.o Hacl_HKDF_Blake2b_256.o Hacl_Streaming_Blake2b_256.o: CFLAGS += $(CFLAGS_256)

all: libevercrypt.$(SO)

# This one and the one below are for people who run "make" without running
# configure. It's not perfect but perhaps a tiny bit better than nothing.
Makefile.config:
	./configure

# If the configure script has not run, create an empty config.h
config.h:
	touch $@

libevercrypt.$(SO): config.h $(OBJS)
	$(CC) $(CFLAGS) -shared -o $@ $(filter-out %.h,$^) $(LDFLAGS)

# 4. Compilation of OCaml bindings; conditional on the presence of the lib_gen
# folder, possibly disabled by configure.

ifeq (,$(DISABLE_OCAML_BINDINGS))
ifneq (,$(wildcard lib_gen))

all:
	dune build -p hacl-star-raw @install

install-hacl-star-raw:
	dune install hacl-star-raw

endif
endif
