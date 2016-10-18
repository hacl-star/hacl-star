all:
	make clean
	$(MAKE) allsubdirs api-kremlin

FSTAR_HOME?=../../FStar
KREMLIN_HOME?=../../kremlin
HACL_HOME?=..
include $(HACL_HOME)/lib/hyperstack/Makefile.include
SUBDIRS=symmetric ec # hash hmac hkdf
allsubdirs: $(addsuffix .all , $(SUBDIRS))

%.all:
	$(MAKE) -C $(basename $@)

test_api.exe:
	mkdir -p tmp
	$(KREMLIN) $(KREMLIN_ARGS) \
		$(HACL_KREMLIN_FILES) $(HACL_API)/Hacl.Box.fst $(KREMTEST)/testlib.c c/test_api.c \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_api.exe -ldopt "-lsodium" # -ccopt "-m32"
	./test_api.exe

perf1: test_api.exe
	./test_api.exe perf1

perf2: test_api.exe
	./test_api.exe perf2

perf3: test_api.exe
	./test_api.exe perf3

clean:
	rm -rf *~ *.exe *.out *.o *.c *.h *.cmi *.cmo *.cmx *.krml ./tmp
	$(MAKE) -C symmetric clean
	$(MAKE) -C ec clean
# 	$(MAKE) -C hash clean
# 	$(MAKE) -C hmac clean
# 	$(MAKE) -C hkdf clean
