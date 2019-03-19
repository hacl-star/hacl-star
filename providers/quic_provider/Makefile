FSTAR_HOME ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
MITLS_HOME ?= ../../../mitls-fstar
MLCRYPTO_HOME ?= ../../../MLCrypto
OPENSSL_HOME ?= $(MLCRYPTO_HOME)/openssl

MARCH?=x86_64

CFLAGS += -fPIC -std=c11 -Ofast -funroll-loops -g -I $(MITLS_HOME)/libs/ffi -D_GNU_SOURCE -D_BSD_SOURCE

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
    EXTRA_PATH = PATH="$(shell cygpath -u $(OPENSSL_HOME)):../../dist/compact:$(PATH)"
    EXTRA_OPTS =
    AR = $(MARCH)-w64-mingw32-ar
    CC = $(MARCH)-w64-mingw32-gcc
else
    LIBQUICCRYPTO=libquiccrypto.so
    UNAME_S := $(shell uname -s)
    AR = ar
    ifeq ($(UNAME_S),Darwin)
	EXTRA_PATH = DYLD_LIBRARY_PATH=$(OPENSSL_HOME):../../dist/compact:.:$(DYLD_LIBRARY_PATH)
        EXTRA_OPTS =
        ARCH = osx
    else
	EXTRA_PATH = LD_LIBRARY_PATH=$(OPENSSL_HOME):../../dist/compact:.:$(LD_LIBRARY_PATH)
        EXTRA_OPTS = -thread -ccopt -fPIC
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

CFLAGS += -I $(KREMLIN_HOME)/include -I ../../dist/evercrypt-external-headers
LDFLAGS += -L ../../dist/compact -levercrypt

ifeq (,$(EVEREST_WINDOWS))
LDFLAGS += -L$(OPENSSL_HOME) -lcrypto
else
LDFLAGS += -lbcrypt
endif

LDFLAGS += $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

.PHONY: all test

all: test

ifeq ($(VS_BIN),)
LIBFILE=
else
LIBFILE=libquiccrypto.lib
$(LIBFILE): $(LIBQUICCRYPTO)
	"$(VS_BIN)/dumpbin.exe" /nologo /exports $(LIBQUICCRYPTO) |  awk -F " " 'BEGIN {print "LIBRARY libquiccrypto"; print "EXPORTS";} $$4 ~/quic_crypto/{print $$4}' > libquiccrypto.def
	"$(VS_BIN)/lib.exe" /nologo /def:libquiccrypto.def /out:$(LIBFILE) /machine:$(LIB_MACHINE)
endif

$(LIBQUICCRYPTO): quic_provider.o
	$(CC) $(CFLAGS) -shared $^ -o $@ $(LDFLAGS)

test.exe: $(LIBQUICCRYPTO) test.o
	$(CC) $(CFLAGS) test.o -o test.exe -L . -lquiccrypto $(LDFLAGS)

benchmark.exe: $(LIBQUICCRYPTO) timing.o benchmark.o
	$(CC) $(CFLAGS) timing.o benchmark.o -o benchmark.exe -L. -lquiccrypto $(LDFLAGS)

benchmark: benchmark.exe
	$(EXTRA_PATH) ./benchmark.exe

test: test.exe
	$(EXTRA_PATH) ./test.exe

# $(LIBQUICCRYPTO) $(LIBFILE)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -fr tmp *.[oa] *.so *.cm[ixoa] *.cmxa *.exe *.dll *.so *.annot *.lib *.def *.exp *~

