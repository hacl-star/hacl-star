KREMLIN_HOME ?= ../../../../kremlin

-include Makefile.include

EVERCRYPT_HOME=../../dist/gcc-compatible
MLCRYPTO_HOME?=../../../../MLCrypto
OPENSSL_HOME=$(MLCRYPTO_HOME)/openssl

CFLAGS = -I $(KREMLIN_HOME)/include -g
LDFLAGS = -L $(EVERCRYPT_HOME) -levercrypt

ifeq (,$(EVEREST_WINDOWS))
LDFLAGS += -L$(OPENSSL_HOME) -lcrypto
else
LDFLAGS += -lbcrypt
endif

ifeq ($(UNAME),Linux)
  LDFLAGS += -Wl,-z,defs,-z,noexecstack,--unresolved-symbols=report-all
endif

all: test

ALL_SOURCES = Test.c

$(info All sources are $(ALL_SOURCES))

LDFLAGS += $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
ifeq ($(OS),Windows_NT)
LDFLAGS += $(EVERCRYPT_HOME)/libevercrypt.dll -lbcrypt
endif

# See https://www.gnu.org/software/make/manual/html_node/Automatic-Prerequisites.html
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(ALL_SOURCES:.c=.d)

Test.exe: $(ALL_SOURCES:.c=.o)
	$(CC) $^ -o $@ $(LDFLAGS)

test: Test.exe
