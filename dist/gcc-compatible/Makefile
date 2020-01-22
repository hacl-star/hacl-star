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

# 1. The usual pseudo auto-configuration

UNAME		= $(shell uname)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC
  VARIANT	= -linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
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
  MLLDFLAGS     += -ccopt -L$(OPENSSL_HOME) -cclib -lcrypto
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

CFLAGS		+= -Wno-parentheses -Wno-deprecated-declarations -g -std=gnu11 -O3

Hacl_Poly1305_128.o Hacl_Chacha20_Vec128.o Hacl_Chacha20Poly1305_128.o: CFLAGS += -mavx
Hacl_Poly1305_256.o Hacl_Chacha20_Vec256.o Hacl_Chacha20Poly1305_256.o: CFLAGS += -mavx -mavx2

all: libevercrypt.$(SO)

libevercrypt.$(SO): $(OBJS)
	$(CC) $(CFLAGS) -shared -o $@ $^ $(LDFLAGS)

# 4. Compilation of OCaml bindings; conditional on the presence of the lib_gen
# folder.

ifneq (,$(wildcard lib_gen))

.PRECIOUS: %.cmx

OCAMLOPT=ocamlfind opt -package ctypes,ctypes.foreign,ctypes.stubs -linkpkg -I lib
OCAMLDEP=ocamlfind dep -I lib -slash

CFLAGS += -I "$(shell ocamlfind query ctypes)" -I "$(shell ocamlfind c -where)"

# Just names.
ALL_OCAML=$(patsubst lib_gen/%_gen.ml,%,$(wildcard lib_gen/*_gen.ml))

ALL_BINDINGS=$(patsubst %,lib/%_bindings.cmx,$(ALL_OCAML))
ALL_GENERATORS=$(patsubst %.ml,%.exe,$(wildcard lib_gen/*_gen.ml))
ALL_ML_STUBS=$(patsubst %,lib/%_stubs.cmx,$(ALL_OCAML))
ALL_C_STUBS=$(patsubst %,lib/%_c_stubs.o,$(ALL_OCAML))

include .depend.ocaml
include ctypes.depend

.depend.ocaml:
	$(OCAMLDEP) $(wildcard lib/*.ml) $(wildcard lib_gen/*.ml) > $@

# Note: for some reason, this minimal Makefile doesn't apply the shortest stem
# rule.
#
# %.exe:
# 	echo long stem
#
# %_foo.exe: %.b
# 	cat $<
#
# %.b:
# 	echo $@ > $@
#
# Which really puzzles me (e.g. make foo_foo.exe always echoes "long stem"),
# even though the shortest stem rule should apply. However, we can cancel a
# previous pattern rule, thanks to
# https://www.gnu.org/software/make/manual/html_node/Canceling-Rules.html
%.exe:

all: libocamlevercrypt.cmxa

lib_gen/%_gen.exe: libevercrypt.a
	$(OCAMLOPT) $(filter-out %.a,$^) libevercrypt.a -o $@ $(MLLDFLAGS)

%.cmx: %.ml
	$(OCAMLOPT) -c $^ -o $@

.PRECIOUS: lib/%_stubs.ml
lib/%_stubs.ml: lib/%_c_stubs.c

ifeq ($(shell uname -s),Darwin)
  DY=DYLD_LIBRARY_
else ifeq ($(OS),Windows_NT)
  DY=
else
  DY=LD_LIBRARY_
endif

lib/%_stubs.ml lib/%_c_stubs.c: lib_gen/%_gen.exe
	$(DY)PATH=.:$(OPENSSL_HOME):$$$(DY)PATH $<

# TODO: Have Kremlin generate the correct order or get it from ctypes.depend
DEPS=lib/Hacl_Hash_stubs.cmx lib/Hacl_Hash_bindings.cmx lib/EverCrypt_AutoConfig2_stubs.cmx lib/EverCrypt_AutoConfig2_bindings.cmx lib/Hacl_Spec_stubs.cmx lib/Hacl_Spec_bindings.cmx lib/EverCrypt_Hash_stubs.cmx lib/EverCrypt_Hash_bindings.cmx lib/Hacl_SHA3_stubs.cmx lib/Hacl_SHA3_bindings.cmx lib/Hacl_Chacha20_stubs.cmx lib/Hacl_Chacha20_bindings.cmx lib/Hacl_Salsa20_stubs.cmx lib/Hacl_Salsa20_bindings.cmx lib/Hacl_Curve25519_64_Slow_stubs.cmx lib/Hacl_Curve25519_64_Slow_bindings.cmx lib/Hacl_Curve25519_64_stubs.cmx lib/Hacl_Curve25519_64_bindings.cmx lib/Hacl_Curve25519_51_stubs.cmx lib/Hacl_Curve25519_51_bindings.cmx lib/Hacl_Ed25519_stubs.cmx lib/Hacl_Ed25519_bindings.cmx lib/Hacl_Poly1305_32_stubs.cmx lib/Hacl_Poly1305_32_bindings.cmx lib/Hacl_Poly1305_128_stubs.cmx lib/Hacl_Poly1305_128_bindings.cmx lib/Hacl_Poly1305_256_stubs.cmx lib/Hacl_Poly1305_256_bindings.cmx lib/Hacl_NaCl_stubs.cmx lib/Hacl_NaCl_bindings.cmx lib/EverCrypt_Error_stubs.cmx lib/EverCrypt_Error_bindings.cmx lib/EverCrypt_CTR_stubs.cmx lib/EverCrypt_CTR_bindings.cmx lib/Hacl_Frodo_KEM_stubs.cmx lib/Hacl_Frodo_KEM_bindings.cmx lib/EverCrypt_OpenSSL_stubs.cmx lib/EverCrypt_OpenSSL_bindings.cmx lib/EverCrypt_Ed25519_stubs.cmx lib/EverCrypt_Ed25519_bindings.cmx lib/Hacl_Chacha20_Vec32_stubs.cmx lib/Hacl_Chacha20_Vec32_bindings.cmx lib/Hacl_Chacha20_Vec128_stubs.cmx lib/Hacl_Chacha20_Vec128_bindings.cmx lib/Hacl_Chacha20Poly1305_128_stubs.cmx lib/Hacl_Chacha20Poly1305_128_bindings.cmx lib/Hacl_Chacha20Poly1305_32_stubs.cmx lib/Hacl_Chacha20Poly1305_32_bindings.cmx lib/Hacl_Chacha20_Vec256_stubs.cmx lib/Hacl_Chacha20_Vec256_bindings.cmx lib/Hacl_Chacha20Poly1305_256_stubs.cmx lib/Hacl_Chacha20Poly1305_256_bindings.cmx lib/EverCrypt_Chacha20Poly1305_stubs.cmx lib/EverCrypt_Chacha20Poly1305_bindings.cmx lib/EverCrypt_AEAD_stubs.cmx lib/EverCrypt_AEAD_bindings.cmx lib/EverCrypt_Vale_stubs.cmx lib/EverCrypt_Vale_bindings.cmx lib/EverCrypt_HMAC_stubs.cmx lib/EverCrypt_HMAC_bindings.cmx lib/EverCrypt_HKDF_stubs.cmx lib/EverCrypt_HKDF_bindings.cmx lib/Hacl_HMAC_stubs.cmx lib/Hacl_HMAC_bindings.cmx lib/Hacl_HKDF_stubs.cmx lib/Hacl_HKDF_bindings.cmx lib/Hacl_HMAC_DRBG_stubs.cmx lib/Hacl_HMAC_DRBG_bindings.cmx lib/EverCrypt_DRBG_stubs.cmx lib/EverCrypt_DRBG_bindings.cmx lib/EverCrypt_Poly1305_stubs.cmx lib/EverCrypt_Poly1305_bindings.cmx lib/EverCrypt_Curve25519_stubs.cmx lib/EverCrypt_Curve25519_bindings.cmx lib/EverCrypt_Cipher_stubs.cmx lib/EverCrypt_Cipher_bindings.cmx lib/EverCrypt_StaticConfig_stubs.cmx lib/EverCrypt_StaticConfig_bindings.cmx

libocamlevercrypt.cmxa: $(ALL_BINDINGS) $(ALL_ML_STUBS) $(ALL_C_STUBS) libevercrypt.$(SO)
	ocamlfind mklib -o ocamlevercrypt $(DEPS) $(ALL_C_STUBS) libevercrypt.a -ccopt -L. -cclib -levercrypt $(MLLDFLAGS)

endif
