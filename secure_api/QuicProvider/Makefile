### This Makefile is no longer used! Makefile.extract builds quicprovider-test.exe

FSTAR_HOME ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
MITLS_HOME ?= ../../../mitls-fstar

MARCH?=x86_64

COPTS = -fPIC -std=c11 -Ofast -funroll-loops -g -I tmp -I $(MITLS_HOME)/libs/ffi -I $(KREMLIN_HOME)/kremlib

ifneq ($(VS140COMNTOOLS),)
	VS_BIN_DOSPATH=$(VS140COMNTOOLS)/../../VC/bin
else ifneq ($(VS120COMNTOOLS),)
	VS_BIN_DOSPATH=$(VS120COMNTOOLS)/../../VC/bin
else ifneq ($(VS120COMNTOOLS),)
	VS_BIN_DOSPATH=$(VS120COMNTOOLS)/../../VC/bin
else ifneq ($(VS110COMNTOOLS),)
	VS_BIN_DOSPATH=$(VS110COMNTOOLS)/../../VC/bin
else
	VS_BIN_DOSPATH=
endif

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

ifeq ($(OS),Windows_NT)
VS_BIN = $(shell cygpath -u "$(VS_BIN_DOSPATH)")
else
VS_BIN =
endif

ifeq ($(PROCESSOR_ARCHITECTURE),AMD64)
LIB_MACHINE=x64
else
LIB_MACHINE=x86
endif

ifeq ($(VS_BIN),)
LIBFILE=
else
LIBFILE=libquiccrypto.lib
$(LIBFILE): $(LIBQUICCRYPTO)
	"$(VS_BIN)/dumpbin.exe" /nologo /exports $(LIBQUICCRYPTO) |  awk -F " " 'BEGIN {print "LIBRARY libquiccrypto"; print "EXPORTS";} $$4 ~/quic_crypto/{print $$4}' > libquiccrypto.def
	"$(VS_BIN)/lib.exe" /nologo /def:libquiccrypto.def /out:$(LIBFILE) /machine:$(LIB_MACHINE)
endif

.PHONY: test dep

all: $(LIBQUICCRYPTO) $(LIBFILE)

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
	rm -fr tmp *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll *.so *.annot *.lib *.def *.exp *~

test.exe: $(LIBQUICCRYPTO) test.o
	$(CC) $(COPTS) -L. test.o -lquiccrypto -o test.exe
