KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

OUT_DIR	      = test-c

KREMLIN=$(KREMLIN_HOME)/krml

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst \
  $(HACL_HOME)/lib/c

FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

%.fst-in:
	@echo $(FSTAR_INCLUDES)	

all: test

ALL_SOURCES = $(HACL_HOME)/lib/c/Lib_PrintBuffer.c

# GNU Make manual section 4.14
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib

CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-infinite-recursion

OBJS = $(HACL_HOME)/lib/c/Lib_PrintBuffer.o $(OUT_DIR)/Loops.o

HACL_LIBS = \
  $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
  $(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
  $(HACL_HOME)/lib/c/Lib.Loops.fst \
  $(HACL_HOME)/lib/fst/Lib.Buffer.fst

$(OUT_DIR)/out.krml: $(HACL_LIBS) Loops.fst
	$(KREMLIN) -tmpdir $(OUT_DIR) \
	-I $(HACL_HOME)/lib -I $(HACL_HOME)/lib/fst \
	-skip-translation $^

$(OUT_DIR)/Loops.c: $(OUT_DIR)/out.krml
	$(KREMLIN) \
	  -add-include '"c/Lib_PrintBuffer.h"' \
	  -add-include '"extracted/TestLib.h"' \
	  -add-include '"kremlin/internal/compat.h"' \
	  -skip-compilation \
	  -bundle 'Lib.*' \
	  -no-prefix 'Loops' \
	  -tmpdir $(OUT_DIR) \
	  $^

$(OUT_DIR)/test.exe: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/out -lkremlib

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

clean:
	rm -rf $(OUT_DIR)
