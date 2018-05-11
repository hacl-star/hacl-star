KOPTS+=-add-early-include '"FStar_UInt128.h"'
KOPTS+=-fnouint128 -drop FStar.UInt128 -falloca -ftail-calls
CFLAGS+=-DKRML_NOUINT128 -DKRML_SEPARATE_UINT128 # -DKRML_NOSTRUCT_PASSING


extract-c: uint128-c/FStar_UInt128.h


uint128-c/FStar_UInt128.h:
	mkdir -p $(dir $@)
	$(KREMLIN_HOME)/krml $(KREMLIN_ARGS) -minimal -fnouint128 -fparentheses \
	  $(FSTAR_HOME)/ulib/FStar.UInt128.fst \
	  -add-early-include '<stdbool.h>' \
	  -add-early-include '<inttypes.h>' \
	  -tmpdir uint128-c -skip-compilation \
	  -bundle FStar.UInt128=FStar.*,Prims # -fnostruct-passing


clean:
	rm -rf *~
	rm -rf uint128-c
