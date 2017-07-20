include ../../../Makefile.include

# Override to get cross-compilation
MARCH?=$(shell uname -m)
UNAME?=$(shell uname | cut -c 1-6)
SED?=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)

ifeq ($(UNAME),CYGWIN)
  CC=$(MARCH)-w64-mingw32-gcc
  AR=x86_64-w64-mingw32-ar
else ifeq ($(MARCH),i686)
  CC=gcc -m32
  AR=ar
else
  CC=gcc
  AR=ar
endif

ifeq ($(UNAME),Darwin)
  VARIANT=-Darwin
else ifeq ($(UNAME),Linux)
  VARIANT=-Linux
endif

ifeq ($(OS),Windows_NT)
  FPIC =
else
  ifeq ($(UNAME),Darwin)
    FPIC =
  else
    FPIC =-fPIC
  endif
endif


VALE_HOME?=../../../../vale
KREMLIN_HOME?=../../../../kremlin
CCOPTS=$(FPIC) -Wall -Wextra -Werror -I $(KREMLIN_HOME)/kremlib
CC:=$(CC) $(CCOPTS)


all: vale.a

ALL_OBJ=Vale_Hash_SHA2_256.o sha256-$(MARCH)$(VARIANT).o sha256_main_i.o \
  aes-$(MARCH)$(VARIANT).o vale_aes_glue.o

vale.a: $(ALL_OBJ)
	ar -cr $@ $^

%.o: %.S
	$(CC) -c $< -o $@

%.o: %.c
	$(CC) -c $< -o $@

# All the Vale files we need to bring into this directory for the compilation of
# our wrappers to be standalone; note that HACL*'s CI does NOT bring Vale into
# the picture, so this directory should compile WITHOUT
# -I$(VALE_HOME)/obj/crypto/hashing
VALE_OBJ_FILES=sha256_main_i.c sha256_main_i.h Prims.h
VALE_UTIL_FILES=DafnyLib.h

.PHONY: import
import:
	@if [ x"$(VALE_HOME)" = x ]; then echo "VALE_HOME not defined"; exit 1; fi
	cp $(VALE_HOME)/obj/aes-gcc.S aes-x86_64.S
	cp $(VALE_HOME)/obj/sha256-gcc.S sha256-x86_64.S
	cp $(VALE_HOME)/obj/aes-macos.S aes-x86_64-Darwin.S
	cp $(VALE_HOME)/obj/sha256-macos.S sha256-x86_64-Darwin.S
	cp $(VALE_HOME)/obj/aes-linux.S aes-x86_64-Linux.S
	cp $(VALE_HOME)/obj/sha256-linux.S sha256-x86_64-Linux.S
	$(SED) -i 's/.section .text/.text/' *.S
	for f in $(VALE_OBJ_FILES); do cp $(VALE_HOME)/obj/crypto/hashing/$$f .; done
	for f in $(VALE_UTIL_FILES); do cp $(VALE_HOME)/src/lib/util/$$f .; done

clean:
	rm -f *.a *.o *~
