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
MARCH		?= $(shell uname -m | sed 's/amd64/x86_64/')
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
else ifeq ($(UNAME),FreeBSD)
  CFLAGS	+= -fPIC
  VARIANT	= -linux
  SO 		= so
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
ifneq (,$(wildcard internal/EverCrypt_OpenSSL.h))
  CFLAGS	+= -I $(OPENSSL_HOME)/include
  LDFLAGS 	+= -L$(OPENSSL_HOME) -lcrypto
ifneq ($(OS),Windows_NT)
  LDFLAGS	+= -ldl -lpthread
endif
  SOURCES	+= evercrypt_openssl.c
endif

ifneq (,$(wildcard internal/EverCrypt_BCrypt.h))
  LDFLAGS	+= -lbcrypt
  SOURCES	+= evercrypt_bcrypt.c
endif

OBJS 		+= $(patsubst %.S,%.o,$(wildcard *-$(MARCH)$(VARIANT).S))

include Makefile.basic

CFLAGS		+= -Wno-parentheses -Wno-deprecated-declarations -Wno-\#warnings -Wno-error=cpp -Wno-cpp -g -std=gnu11 -O3

Hacl_Poly1305_128.o Hacl_Streaming_Poly1305_128.o Hacl_Chacha20_Vec128.o Hacl_Chacha20Poly1305_128.o Hacl_Hash_Blake2s_128.o Hacl_HMAC_Blake2s_128.o Hacl_HKDF_Blake2s_128.o Hacl_Streaming_Blake2s_128.o Hacl_SHA2_Vec128.o: CFLAGS += $(CFLAGS_128)
Hacl_Poly1305_256.o Hacl_Streaming_Poly1305_256.o Hacl_Chacha20_Vec256.o Hacl_Chacha20Poly1305_256.o Hacl_Hash_Blake2b_256.o Hacl_HMAC_Blake2b_256.o Hacl_HKDF_Blake2b_256.o Hacl_Streaming_Blake2b_256.o Hacl_SHA2_Vec256.o: CFLAGS += $(CFLAGS_256)

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

.PRECIOUS: %.cmx

OCAMLOPT=ocamlfind opt -package ctypes,ctypes.stubs -linkpkg -I lib
OCAMLDEP=ocamlfind dep -I lib -slash

OCAMLC=ocamlfind c -g -package ctypes,ctypes.stubs -linkpkg -I lib

CFLAGS += -I "$(shell ocamlfind query ctypes)" -I "$(shell ocamlfind c -where)"

# Don't include bindings for files that cannot be compiled.
BLACKLIST_ML=$(patsubst %.c,%,$(BLACKLIST))
ALL_OCAML=$(filter-out $(BLACKLIST_ML),$(patsubst lib_gen/%_gen.ml,%,$(wildcard lib_gen/*_gen.ml)))

# Just names.
ALL_BINDINGS=$(patsubst %,lib/%_bindings.cmx,$(ALL_OCAML))
ALL_GENERATORS=$(patsubst %,lib_gen/%_gen.exe, $(ALL_OCAML))
ALL_ML_STUBS=$(patsubst %,lib/%_stubs.cmx,$(ALL_OCAML))
ALL_C_STUBS=$(patsubst %,lib/%_c_stubs.o,$(ALL_OCAML))

include .depend.ocaml
include ctypes.depend

lib_gen/Lib_RandomBuffer_System_gen.cmx: lib/Lib_RandomBuffer_System_bindings.cmx
lib_gen/Lib_RandomBuffer_System_gen.exe: lib/Lib_RandomBuffer_System_bindings.cmx lib_gen/Lib_RandomBuffer_System_gen.cmx

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

all: ocamlevercrypt.cmxa

lib_gen/%_gen.exe: libevercrypt.a
	$(OCAMLOPT) $(filter-out %.a,$^) libevercrypt.a -o $@

%.cmx: %.ml
	$(OCAMLOPT) -c $^ -o $@

%.cmo: %.ml
	$(OCAMLC) -c $^ -o $@


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
	$<

# Compiling these files raises the pointer sign warning because the Ctypes declaration for bytes expects a char*, not a uint8_t*
# Can be remove once ctypes is upgraded to 0.17
lib/%_c_stubs.o: CFLAGS += -Wno-pointer-sign

BLACKLIST_CMX =  $(patsubst %,lib/%_stubs.cmx,$(BLACKLIST_ML))
BLACKLIST_CMX += $(patsubst %,lib/%_bindings.cmx,$(BLACKLIST_ML))
CTYPES_CMX    =  $(filter-out $(BLACKLIST_CMX),$(CTYPES_DEPS))
CTYPES_CMX    += lib/Lib_RandomBuffer_System_stubs.cmx lib/Lib_RandomBuffer_System_bindings.cmx
CTYPES_ML     =  $(patsubst %.cmx,%.ml,$(CTYPES_CMX))
CTYPES_CMI    =  $(patsubst %.cmx,%.cmi,$(CTYPES_CMX))
CTYPES_CMO    = $(patsubst %.cmx,%.cmo,$(CTYPES_CMX))


ocamlevercrypt.cma: $(ALL_BINDINGS) $(CTYPES_CMO) $(ALL_C_STUBS) $(CTYPES_CMX) libevercrypt.$(SO)
	ocamlmklib -o ocamlevercrypt $(CTYPES_CMO) -L. -levercrypt

ocamlevercrypt.cmxa: $(ALL_BINDINGS) $(ALL_ML_STUBS) $(ALL_C_STUBS) libevercrypt.$(SO)
	ocamlmklib -o ocamlevercrypt $(CTYPES_CMX) -L. -levercrypt

STUBLIBS_PATH=$(OPAM_SWITCH_PREFIX)/lib/stublibs

dllocamlevercrypt.$(SO): ocamlevercrypt.cmxa ocamlevercrypt.cma
	ocamlmklib -o ocamlevercrypt $(ALL_C_STUBS) -L. -L$(STUBLIBS_PATH) -levercrypt

install-hacl-star-raw: dllocamlevercrypt.$(SO)
	ocamlfind remove hacl-star-raw || true && \
         ocamlfind install hacl-star-raw META $(CTYPES_ML) $(CTYPES_CMX) $(CTYPES_CMO) $(CTYPES_CMI) \
         libevercrypt.a libevercrypt.$(SO) ocamlevercrypt.cma ocamlevercrypt.cmxa ocamlevercrypt.a \
         libocamlevercrypt.a dllocamlevercrypt.$(SO) config.h

.PHONY: install-ocaml
install-ocaml: install-hacl-star-raw
	cd ../../bindings/ocaml && dune build && dune install

endif
endif
