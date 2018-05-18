EVERCRYPT_HOME ?= ../
KREMLIN_HOME   ?= ../../../kremlin

UNAME = $(shell uname)

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    EVERCRYPT_HOME_RUN := $(shell cygpath -a -u ${EVERCRYPT_HOME})
    MLCRYPTO_HOME_RUN := $(shell cygpath -a -u ${MLCRYPTO_HOME})
  else
    EVERCRYPT_HOME_RUN := $(EVERCRYPT_HOME)
    MLCRYPTO_HOME_RUN := $(MLCRYPTO_HOME)
  endif
  PREFIX = PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(PATH)
else ifeq ($(UNAME),Darwin)
  PREFIX = DYLD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  PREFIX = LD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(LD_LIBRARY_PATH)
endif

test: sample-project.exe
	$(PREFIX) ./sample-project.exe

sample-project.exe: SampleProject.fst
	krml -ldopts -L../out,-levercrypt -tmpdir out \
	  -I ../multiplexer -I $(KREMLIN_HOME)/include/kremlin \
	  -add-include '"testlib.h"' $(KREMLIN_HOME)/kremlib/testlib.c \
	  -no-prefix SampleProject -o sample-project.exe \
	  $(KREMLIN_HOME)/kremlib/kremstr.c \
	  SampleProject.fst \

clean:
	rm -rf out sample-project.exe SampleProject.fst.checked.lax

%.fst-in:
	@echo --include ../multiplexer --include $(KREMLIN_HOME)/kremlib
