FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = curve25519-c
OUT_DIR	      = curve25519-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: test

test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage1: $(GENERATED_DIR)/Hacl_Curve25519_51.c \
	$(GENERATED_DIR)/Hacl_Curve25519_64.c


stage2: curve25519_51.exe curve25519_64.exe
	./curve25519_51.exe \
	./curve25519_64.exe \

curve25519_51.exe: $(GENERATED_DIR)/Hacl_Curve25519_51.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/minimal -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(GENERATED_DIR)/Hacl_Curve25519_51.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o curve51-test.c -o curve25519_51.exe
	./curve25519_51.exe

boringssl_x25519.exe: boringssl-test.c
#	$(CC) -march=native -mtune=native -flto -O3 -I $(HACL_HOME)/../boringssl/include boringssl-test.c -o boringssl_x25519.exe $(HACL_HOME)/../boringssl/build/crypto/libcrypto.a -lpthread
	$(CC) -march=native -mtune=native -flto -O3 -I $(HACL_HOME)/../boringssl/include boringssl-test.c -o boringssl_x25519.exe $(HACL_HOME)/other_providers/openssl/libcrypto.a
	./boringssl_x25519.exe

curve25519_64.exe: $(GENERATED_DIR)/Hacl_Curve25519_64.c vale_25519.h 
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/minimal -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(GENERATED_DIR)/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o curve64-test.c -o curve25519_64.exe 
	./curve25519_64.exe

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/lib \
  ./lemmas \

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --odir $(OUTPUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.Curve25519_51.fst Hacl.Curve25519_64.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar -LowStar -Spec' > $@

include .depend


$(HINT_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

KREMLIN_TESTLIB=-fbuiltin-uint128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces \
	-funroll-loops 8 -warn-error +9 -add-include '"kremlib.h"' -add-include '"FStar_UInt_8_16_32_64.h"' $(KREMLIB)/dist/minimal/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

# 2. Generation of .c files

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Hacl_Curve25519_51.c: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation  \
	-library 'C,FStar' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-bundle 'Hacl.Curve25519_51=Hacl.Impl.*' \
	-drop 'FStar.UInt128,LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.*,Hacl.Curve25519_64' \
	-tmpdir $(GENERATED_DIR) \
	$^

$(GENERATED_DIR)/Hacl_Curve25519_64.c: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-add-include '"vale_25519.h"' \
	-library 'C,FStar' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-bundle 'Hacl.Curve25519_64=Hacl.Impl.*' \
	-drop 'FStar.UInt128,Hacl.Impl.Curve25519.Field64.Core,LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.*,Hacl.Curve25519_51' \
	-no-prefix  Hacl.Impl.Curve25519.Field64.Core \
	-tmpdir $(GENERATED_DIR) \
	$^

# The Makefile is manually staged because GNU Make does not understand
# dependencies between the Makefiles we include, i.e. it won't first generate
# the .depend, parse it, then generate Makefile.include, parse it, then
# generate dependencies among the C files
ifeq ($(STAGE),2)

# 3. Collecting all of our source files, and generating corresponding object
# files.

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(KREMLIN_HOME)/kremlib/c \
  $(KREMLIN_HOME)/kremlib/dist/minimal \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/c

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable

# GNU Make manual section 4.14

curve25519_64_vale.exe: $(GENERATED_DIR)/Hacl_Curve25519_64.c vale_25519.h vale/obj/curve25519-x86_64-darwin.S
	$(CC) -march=native -mtune=native -flto -O3 vale/obj/curve25519-x86_64-darwin.S -c -o vale25519.o 
	$(CC) -march=native -mtune=native -flto -O3 -I $(KREMLIN_HOME)/kremlib/dist/minimal -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(GENERATED_DIR)/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o curve64-test.c -o curve25519_64_vale.exe vale25519.o 
	./curve25519_64_vale.exe

curve25519_64_v_inline.exe: $(GENERATED_DIR)/Hacl_Curve25519_64.c rfc7748_25519.h
	cp -f vale_25519.h tmp_25519.h
	cp -f vale-inline.h vale_25519.h
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/minimal -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(GENERATED_DIR)/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o curve64-test.c -o curve25519_64_v_inline.exe 
	cp -f tmp_25519.h vale_25519.h
	./curve25519_64_v_inline.exe

curve25519_64_mixed.exe: $(GENERATED_DIR)/Hacl_Curve25519_64.c rfc7748_25519.h
	cp -f vale_25519.h tmp_25519.h
	cp -f rfc7748_25519.h vale_25519.h
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/minimal -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(GENERATED_DIR)/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o curve64-test.c -o curve25519_64_mixed.exe 
	cp -f tmp_25519.h vale_25519.h
	./curve25519_64_mixed.exe

curve25519_64_rfc.exe: $(GENERATED_DIR)/Hacl_Curve25519_64.c
	$(CC) -march=native -mtune=native -O3 -I rfc7748_src/ rfc7748_src/fp25519_x64.c -c -o fp25519.o 
	$(CC) -march=native -mtune=native -O3 -I rfc7748_src/ rfc7748_src/x25519_x64.c -c -o x25519.o 
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/minimal -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o curve64-rfc-test.c -o curve25519_64_rfc.exe fp25519.o x25519.o
	./curve25519_64_rfc.exe

curve25519_64.exe: curve25519_64_vale.exe curve25519_64_mixed.exe curve25519_64_rfc.exe
	./curve25519_64_vale.exe
	./curve25519_64_rfc.exe
	./curve25519_64_mixed.exe



%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))


.PRECIOUS: %.o

endif # STAGE=2

# 5. Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 6. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a
	rm -rf include/*.o include/*.d

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

distclean: clean
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked
