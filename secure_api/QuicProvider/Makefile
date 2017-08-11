FSTAR_HOME ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
MITLS_HOME ?= ../../../mitls-fstar

MARCH?=x86_64

COPTS = -fPIC -std=c11 -DKRML_NOUINT128 -I tmp -I $(MITLS_HOME)/libs/ffi -I $(KREMLIN_HOME)/kremlib

ifeq ($(OS),Windows_NT)
    LIBQUICCRYPTO=libquiccrypto.dll
    # On cygwin + cygwinports, DLLs are searched in the PATH, which is not
    # altered to include by default the mingw64 native DLLs. We also need to
    # find dllcorecrypto.dll; it is in the current directory, which Windows
    # always uses to search for DLLs.
    EXTRA_PATH = PATH="/usr/$(MARCH)-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
    ARCH = win32
    EXTRA_OPTS =
    EXTRA_LIBS = -L.
    AR = $(MARCH)-w64-mingw32-ar
    CC = $(MARCH)-w64-mingw32-gcc
else
    LIBQUICCRYPTO=libquiccrypto.so
    EXTRA_PATH = LD_LIBRARY_PATH=.
    UNAME_S := $(shell uname -s)
    AR = ar
    ifeq ($(UNAME_S),Darwin)
        EXTRA_OPTS =
        EXTRA_LIBS = -L.
        ARCH = osx
    else
        EXTRA_OPTS = -thread -ccopt -fPIC
        EXTRA_LIBS = -L.
        ARCH = x86_64
    endif
endif

.PHONY: test dep

all: $(LIBQUICCRYPTO)

tmp:
	$(MAKE) -C .. QuicProvider-tmp

../vale/asm/vale.a:
	$(MAKE) -C ../vale/asm

libhacl.a: tmp ../vale/asm/vale.a
	cp ../vale/asm/vale.a libhacl.a
	$(AR) -cr libhacl.a tmp/*.o

%.o: %.c
	$(CC) $(COPTS) -c $< -o $@

$(LIBQUICCRYPTO): libhacl.a quic_provider.o
	$(CC) $(COPTS) -shared -L. quic_provider.o -lhacl -o $@

clean:
	rm -fr tmp *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll *.so *.annot *~

test.exe: $(LIBQUICCRYPTO) test.o
	$(CC) $(COPTS) -L. test.o -lquiccrypto -o test.exe
