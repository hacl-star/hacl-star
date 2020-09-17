# This is the Makefile that will build the distribution of EverCrypt.
#
# ./configure has to be run before this Makefile can be used. This file does NOT
# configure the build but only runs it.
#
# This Makefile may (conservatively) link in some Vale assemblies that may end
# up un-needed in the final shared object.
#
# Additionally, this Makefile works out of the box on Linux, OSX and
# Cygwin/MinGW.
#
# The Makefile produces:
# - libevercrypt.so, a shared object where unused symbols have been removed
# - libevercrypt.a

# Include the configuration generated with ./configure
include Makefile.config

# Include platform specific files
OBJS 		+= $(patsubst %.S,%.o,$(wildcard *-$(MARCH)$(VARIANT).S))

include Makefile.basic

# Set default CFLAGS
CFLAGS	  	+= -Wno-parentheses -Wno-deprecated-declarations -Wno-\#warnings -Wno-error=cpp -Wno-cpp -g -std=gnu11 -O3
CFLAGS_128  ?= -mavx
CFLAGS_256  ?= -mavx -mavx2

# Include CFLAGS for vectorized implementations
Hacl_Poly1305_128.o Hacl_Chacha20_Vec128.o Hacl_Chacha20Poly1305_128.o Hacl_Blake2s_128.o Hacl_HMAC_Blake2s_128.o Hacl_HKDF_Blake2s_128.o Hacl_Streaming_Blake2s_128.o: CFLAGS += $(CFLAGS_128)
Hacl_Poly1305_256.o Hacl_Chacha20_Vec256.o Hacl_Chacha20Poly1305_256.o Hacl_Blake2b_256.o Hacl_HMAC_Blake2b_256.o Hacl_HKDF_Blake2b_256.o Hacl_Streaming_Blake2b_256.o: CFLAGS += $(CFLAGS_256)

# Build everything
all: libevercrypt.$(SO)

# Build the shared library
libevercrypt.$(SO): $(OBJS)
	$(CC) $(CFLAGS) -shared -o $@ $(filter-out %.h,$^) $(LDFLAGS)


# Compilation of OCaml bindings; conditional on the presence of the lib_gen
# folder, possibly disabled by configure.

ifeq (,$(DISABLE_OCAML_BINDINGS))
ifneq (,$(wildcard lib_gen))

.PRECIOUS: %.cmx

OCAMLOPT=ocamlfind opt -package ctypes,ctypes.foreign,ctypes.stubs -linkpkg -I lib
OCAMLDEP=ocamlfind dep -I lib -slash

OCAMLC=ocamlfind c -g -package ctypes,ctypes.foreign,ctypes.stubs -linkpkg -I lib

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

ocamlevercrypt.cmxa: $(ALL_BINDINGS) $(ALL_ML_STUBS) $(ALL_C_STUBS) libevercrypt.$(SO)
	ocamlfind mklib -o ocamlevercrypt $(CTYPES_CMX) $(ALL_C_STUBS) -ccopt -L. -cclib -levercrypt

CTYPES_CMO    = $(patsubst %.cmx,%.cmo,$(CTYPES_CMX))
ALL_ML_STUBS_CMO = $(patsubst %.cmx,%.cmo,$(ALL_ML_STUBS))

ocamlevercrypt.cma: $(ALL_BINDINGS) $(ALL_ML_STUBS_CMO) $(CTYPES_CMO) $(ALL_C_STUBS) libevercrypt.$(SO)
	ocamlfind mklib -o ocamlevercrypt $(CTYPES_CMO) $(ALL_C_STUBS) -ccopt -L. -cclib -levercrypt

install-hacl-star-raw: ocamlevercrypt.cmxa ocamlevercrypt.cma libevercrypt.a
	ocamlfind install hacl-star-raw META $(CTYPES_ML) $(CTYPES_CMX) $(CTYPES_CMO) $(CTYPES_CMI) ocamlevercrypt.cma ocamlevercrypt.cmxa *.a *.$(SO) config.h

endif
endif