FSTAR_HOME?=../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../../Makefile.include

RSA_FILES= \
	RSA.fst \
	Test.RSA.fst  

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --include ../../../code/lib/kremlin \
	--include $(KREMLIN_HOME)/kremlib --include ../../../specs --include ../../hash --lax

%.fst-verify: %.fst
	$(FSTARB) $^

verify: $(addsuffix -verify, $(RSA_FILES))

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
INCLUDES= -I ../../../code/lib/kremlin -I $ ../../../specs \
  -I $(KREMLIN_HOME)/kremlib -I ../../../code/hash
KRML=$(KRML_BIN) $(KREMLIN_ARGS) -verbose $(INCLUDES) \
  -drop Prims,FStar,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
  -drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.* \
  $(KREMLIN_HOME)/kremlib/testlib.c \
  -add-include '"testlib.h"' -ccopt -march=native

# Extraction

extract-c: rsa-c/RSA.c

test: test-rsa.exe
	
rsa-c/out.krml: RSA.fst Test.RSA.fst
	$(KRML) -tmpdir rsa-c -skip-translation $^

EXTRACTED = \
	Hacl_Hash_Lib_LoadStore \
	Hacl_Hash_Lib_Create \
	Hacl_Hash_SHA2_256 \
	SHA2_256 \
	RSA \
	Test_RSA 
	
$(addprefix rsa-c/,$(addsuffix .c, $(EXTRACTED))): rsa-c/out.krml
	$(KRML) -tmpdir rsa-c $^ -skip-compilation -no-prefix Test.RSA
  
CC := $(CC) $(INCLUDES)

%.o: %.c
	$(CC) -c $< -o $@

BASE_OBJ = $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o

test-rsa.exe: $(addprefix rsa-c/,$(addsuffix .o, $(EXTRACTED))) $(BASE_OBJ)
	$(CC) -o $@ $^
	./test-rsa.exe