FSTAR_HOME   ?= ../../../FStar
HACL_HOME    ?= ../../
FSTAR_EXE    := $(if $(shell PATH=$(PATH) which "fstar.exe"),$(shell PATH=$(PATH) which "fstar.exe"),$(FSTAR_HOME)/bin/fstar.exe)

OUTPUT_DIR    = .output

FSTAR_INCLUDE_DIRS = \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --odir $(OUTPUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

%.fst-in:
	@echo $(FSTAR_FLAGS)

%.fsti-in:
	@echo $(FSTAR_FLAGS)
