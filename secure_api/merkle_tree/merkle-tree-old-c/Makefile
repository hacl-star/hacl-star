FSTAR=fstar.exe
KREMLIN=Kremlin.native

EXT_DIR=./ext

TARGETS=../MerkleTree.New.Low.fst \
  ../../../providers/evercrypt/fst/EverCrypt.Hash.fst

.PHONY: new clean

new:
	$(KREMLIN) $(TARGETS) \
	-no-prefix 'MerkleTree.New.Low' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'EverCrypt.Hash,Hacl.Impl.*' \
	-drop WasmSupport \
	-tmpdir $(EXT_DIR) \
	-I ../ \
	-I ../../../providers/evercrypt/ \
	-I ../../../providers/evercrypt/fst/ \
	-I ../../../providers/evercrypt/config/default/ \
	-I ../../../code/hash/ \
	-I ../../../code/lib/ \
	-I ../../../specs/ \
	-I ../../../../kremlin/kremlib/compat/
# -I ../../../../kremlin/kremlib/ \

clean:
	rm -f a.out
	rm -rf ./ext/*
