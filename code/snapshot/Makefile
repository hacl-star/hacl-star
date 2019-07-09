FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

OUTPUT_DIR = .output
GENERATED_DIR = ../dump

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/code/curve25519 \
  $(HACL_HOME)/code/curve25519/lemmas \

FSTAR_FLAGS = --cmi \
  --cache_checked_modules --odir $(OUTPUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

SNAPSHOT=Tezos.fst

all:
	make $(GENERATED_DIR)/Tezos.c

.depend:
	$(FSTAR) --dep full $(SNAPSHOT) --extract '* -Prims -FStar -LowStar -Spec' > $@

include .depend

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

KREMLIN_TESTLIB=-fbuiltin-uint128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces \
	-funroll-loops 8 -warn-error +9 -add-include '"kremlib.h"' -add-include '"FStar_UInt_8_16_32_64.h"' $(KREMLIB)/dist/minimal/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

$(GENERATED_DIR)/Tezos.c: .output/Tezos.krml | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation  \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-drop 'FStar.UInt128,LowStar,Spec,Prims,Lib,C.Loops.*,C.*,C,FStar.*,Hacl.Spec.*' \
	-tmpdir $(GENERATED_DIR) \
	$^
