HACL_HOME=../..
include $(HACL_HOME)/Makefile.common

CC = gcc-9.1
all: dist/libsha3.a


# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

FSTAR_ROOTS = Hacl.SHA3.fst
# P256_BUNDLE=-bundle Hacl.Impl.P256.PointDouble=Hacl.Impl.ECDSA.*,Hacl.Impl.SolinasReduction,Hacl.Impl.P256.*

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I ../../../lib/c -I . -march=native -mtune=native -O3
export CFLAGS

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libsha3.a $(BASE_FLAGS) \
	  -tmpdir dist \
	  -fbuiltin-uint128 \
	  -funroll-loops 12 \
	  -add-include '"lib_intrinsics.h"' \
	  -skip-compilation

# An archive with all the compiled code in this directory.
# We don't want Hacl_Test_ECDSA.o to be included so we redefine OBJS
dist/libsha3.a:dist/Hacl_SHA3.o
	$(MAKE) -C dist -f Makefile.basic OBJS=$(notdir $^) $(notdir $@)
	
dist/%.o: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic $(notdir $@)