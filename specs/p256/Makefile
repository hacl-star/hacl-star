HACL_HOME=../..

# Needed to remove FStar.Math.Euclid from --alread_cached
.depend: FSTAR_NO_FLAGS = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_HINTS) \
  --odir $(OUTPUT_DIR) --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --already_cached 'Prims FStar -FStar.Math.Euclid LowStar C Spec.Loops TestLib WasmSupport' --warn_error '+241@247-272' \
  --cache_dir $(OUTPUT_DIR) --trivial_pre_for_unannotated_effectful_fns false

all: ../../obj/Spec.P256.Jacobian.fst.checked

include ../../Makefile.local
