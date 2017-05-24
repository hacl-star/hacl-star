# Basic tool detection
UNAME=$(shell uname)
ifeq ($(UNAME),Linux)
  SHA_S=$(VALE_HOME)/obj/sha256-linux.S
  AR=ar
else
  ifeq ($(UNAME),Darwin)
    SHA_S=$(VALE_HOME)/obj/sha256-macos.S
    AR=ar
  else
    # mingw64
    SHA_S=$(VALE_HOME)/obj/sha256-gcc.S
    AR=x86_64-w64-mingw32-ar
    CC=x86_64-w64-mingw32-gcc
  endif
endif

# Paths and include directories
VALE_HOME?=../../../vale
KREMLIN_HOME?=../../../kremlin
CCOPTS=-Wall -Wextra -Werror \
  -I$(VALE_HOME)/obj/crypto/hashing -I$(KREMLIN_HOME)/kremlib \
  -I$(VALE_HOME)/src/lib/util
CC:=$(CC) $(CCOPTS)

all: vale.a

vale.a: Vale_Hash_SHA2_256.o sha_asm.o $(VALE_HOME)/obj/crypto/hashing/sha256_main_i.o
	ar -cr $@ $^

sha_asm.s: $(SHA_S)
	cp -f $< $@

%.o: %.s
	$(CC) -c $< -o $@

%.o: %.c
	$(CC) -c $< -o $@

clean:
	rm -rf *.o *.a
