EVERCRYPT_HOME ?= ../
KREMLIN_HOME   ?= ../../../kremlin

UNAME = $(shell uname)

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    EVERCRYPT_HOME_RUN := $(shell cygpath -a -u ${EVERCRYPT_HOME})
  else
    EVERCRYPT_HOME_RUN := $(EVERCRYPT_HOME)
  endif
  PREFIX = PATH=$(EVERCRYPT_HOME)/out
else ifeq ($(UNAME),Darwin)
  PREFIX = DYLD_LIBRARY_PATH=$(EVERCRYPT_HOME)/out
else ifeq ($(UNAME),Linux)
  PREFIX = LD_LIBRARY_PATH=$(EVERCRYPT_HOME)/out
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
