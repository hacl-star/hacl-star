# Find fstar.exe and set FSTAR_EXE to its absolute path.

# If FSTAR_EXE is already externally set, we just use it. Note the use
# of ?= everywhere below.

# If FSTAR_HOME is set, we honor it and pick that F*.
ifdef FSTAR_HOME
FSTAR_EXE ?= $(abspath $(FSTAR_HOME)/bin/fstar.exe)
endif

# Otherwise we try to find it from the PATH.

# Bash's 'type -P' is essentially 'which'. This relies on having bash
# around, but does not require 'which'.
FSTAR_EXE ?= $(shell bash -c 'type -P fstar.exe')

# Force eval
FSTAR_EXE := $(FSTAR_EXE)

# Don't fail if we're cleaning
ifneq ($(MAKECMDGOALS),clean)
ifeq (,$(FSTAR_EXE))
  $(error "Did not find fstar.exe in PATH and FSTAR_EXE/FSTAR_HOME unset, aborting.")
endif
endif

export FSTAR_EXE
