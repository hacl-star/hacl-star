FSTAR_HOME	?= ../FStar
KREMLIN_HOME	?= ../kremlin
HACL_HOME	?= ../..

CACHE_DIR	= .cache
OUTPUT_DIR	= .output
GENERATED_DIR	= generated
OUT_DIR		= out

# 0. The usual pseudo auto-configuration

UNAME		= $(shell uname)
SED		= $(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -Darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC
  VARIANT	= -Linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
else ifeq ($(OS),Windows_NT)
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  SO		= dll
endif

all: $(OUT_DIR)/libevercrypt.a $(OUT_DIR)/libevercrypt.$(SO) $(OUT_DIR)/evercrypt.cmxa

test: sample-project/sample-project.exe
	LD_LIBRARY_PATH=. DYLD_LIBRARY_PATH=. PATH=. ./$<

# 1. Extraction of fsti's and fst's into a set of C files

FSTAR		= $(FSTAR_HOME)/bin/fstar.exe --cache_checked_modules \
  --use_two_phase_tc true \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include $(KREMLIN_HOME)/kremlib --include multiplexer \
  --include multiplexer/fst \
  --use_hints # --record_hints --hint_info

ROOTS		= EverCrypt.fst EverCrypt.Bytes.fsti

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract Kremlin > $@

include .depend

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# Force linearization of the krml invocation because it generates multiple files
# at the same time.
$(GENERATED_DIR)/EverCrypt_Helpers.c: $(GENERATED_DIR)/EverCrypt.c
multiplexer/c/bytes.o: $(GENERATED_DIR)/EverCrypt.c
multiplexer/c/vale.o: $(GENERATED_DIR)/EverCrypt.c
multiplexer/c/hacl.o: $(GENERATED_DIR)/EverCrypt.c
multiplexer/c/native.o: $(GENERATED_DIR)/EverCrypt.c

$(GENERATED_DIR)/EverCrypt.c: $(ALL_KRML_FILES) | .depend
	$(KREMLIN_HOME)/krml -skip-compilation -minimal \
	  -add-include '"kremlib.h"' -add-include '"kremlin/c_string.h"' \
	  -bundle 'FStar.*,Prims,C.Loops,Spec.Loops' \
	  -tmpdir generated $^ \
	  && \
	touch $@


# 2. Compiling all of that in a shared object

# TODO: grab these directly from Vale and error out with a helpful make target,
# like for HACL*.
VALE_DIR 	= $(HACL_HOME)/secure_api/vale/asm
VALE_SOURCES	= $(addprefix $(VALE_DIR)/,sha256_main_i.c \
  vale_aes_glue.c Vale_Hash_SHA2_256.c)
VALE_ASM 	= $(addprefix $(VALE_DIR)/,\
  sha256-$(MARCH)$(VARIANT).S aes-$(MARCH)$(VARIANT).S)

# TODO: understand why these two targets are broken/possibly switch to a HACL*
# branch where their compilation is restored.
# - aead-c: kremlin seems to generate an extra argument, JK had a hack to sed
#   the code in place
HACL_DIR	= $(HACL_HOME)/code
HACL_SOURCES	= \
  $(HACL_DIR)/salsa-family/chacha-c/Hacl_Chacha20.c \
  $(HACL_DIR)/salsa-family/salsa-c/Hacl_Salsa20.c \
  $(addprefix $(HACL_DIR)/hash/sha2-c/Hacl_SHA2_,256.c 384.c 512.c) \
  $(HACL_DIR)/curve25519/x25519-c/Hacl_Curve25519.c \
  $(HACL_DIR)/ed25519/ed25519-c/Hacl_Ed25519.c \
  $(HACL_DIR)/poly1305/poly-c/Hacl_Poly1305_64.c \
  $(HACL_DIR)/hmac/hmac-c/Hacl_HMAC_SHA2_256.c \
  $(HACL_DIR)/poly1305/poly-c/AEAD_Poly1305_64.c \
  $(HACL_DIR)/salsa-family/chacha-vec128-c/Hacl_Chacha20_Vec128.c \
  #$(HACL_DIR)/api/aead-c/Chacha20Poly1305.c \

EVERCRYPT_SOURCES = \
  $(addprefix $(GENERATED_DIR)/,EverCrypt.c EverCrypt_Helpers.c) \
  $(addprefix multiplexer/c/,native.c vale.c hacl.c bytes.c)

ALL_SOURCES	= $(HACL_SOURCES) $(VALE_SOURCES) $(EVERCRYPT_SOURCES)
ALL_OBJS	= $(patsubst %.c,%.o,$(ALL_SOURCES)) $(patsubst %.S,%.o,$(VALE_ASM))

INCLUDE_DIRS	= $(foreach c,$(ALL_SOURCES),$(dir $(c))) \
  $(HACL_HOME)/secure_api/out/runtime_switch/extracted \
  $(HACL_HOME)/snapshots/common $(KREMLIN_HOME)/include

CFLAGS		+= $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(addsuffix .d,$(ALL_SOURCES))

$(OUT_DIR):
	mkdir -p $@

# Note: see
# https://www.gnu.org/software/make/manual/html_node/Archive-Pitfalls.html#Archive-Pitfalls
# for why we are not using libhacl.a($(OBJS))
$(OUT_DIR)/libevercrypt.a: $(ALL_OBJS) | $(OUT_DIR)
	$(AR) cr $@ $^

$(OUT_DIR)/libevercrypt.$(SO): $(ALL_OBJS) | $(OUT_DIR)
	$(CC) $(LDFLAGS) -shared $^ -o $@

.PRECIOUS: %.o

$(HACL_SOURCES):
	$(error "Please run `make -j 8 -C $(HACL_DIR) extract-c` before invoking this Makefile")

.PHONY: clean
clean:
	rm -rf $(GENERATED_DIR) multiplexer/c/*.o libevercrypt.so libevercrypt.a test/sample-project.exe

.PHONY: distclean
distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR)

# 3. A sample project that is a client of the library; run in a single
# invocation of KreMLin for simplicity; essentially checks that separate linking
# works.

sample-project/sample-project.exe: sample-project/SampleProject.fst $(OUT_DIR)/libevercrypt.so
	$(KREMLIN_HOME)/krml -ldopt -levercrypt $< -no-prefix SampleProject \
	  -I multiplexer/ -add-include '"kremlin/c_string.h"' KRML_HOME/kremlib/testlib.c \
	  -tmpdir .sample-project \
	  -add-include '"kremlin/testlib.h"' -ldopt -Lout -o $@

# 4. An OCaml library that exposes only the bytes-based interface, for now

$(OUT_DIR)/evercrypt.cmxa: multiplexer/ml/EverCrypt_Bytes.ml | $(OUT_DIR)/libevercrypt.$(SO) $(OUT_DIR)
	ocamlfind mklib -package ctypes,ctypes.foreign -ccopt -Wl,-levercrypt \
	  -ccopt -Wl,-L. -o $(patsubst %.cmxa,%,$@) $^
