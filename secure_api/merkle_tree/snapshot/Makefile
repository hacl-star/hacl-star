
all: libmerkletree.a merkle_tree_test

CFLAGS+=-I kremlin/include -I kremlin/kremlib -I kremlin/kremlib/extracted -I evercrypt/include 

THIS_SOURCE=$(wildcard *.c)
EVERCRYPT_SRC=$(wildcard evercrypt/extracted/*.c)
KREMLIB_SRC=$(wildcard kremlin/kremlib/extracted/*.c) $(wildcard kremlin/*.c)
HACL_SRC=$(wildcard hacl/*.c)
VALE_SRC=$(wildcard vale/*.c)
VALE_ASM=$(wildcard vale/*.S)
ALL_OBJS=$(patsubst %.c,%.o,$(THIS_SOURCE) $(EVERCRYPT_SRC) $(KREMLIB_SRC) $(HACL_SRC) $(VALE_SRC)) $(patsubst %.S,%.o,$(VALE_ASM))
NOT_NEEDED=kremlin/kremlib/extracted/FStar_UInt128.o kremlin/fstar_uint128_msvc.o merkle_tree_test.o

libmerkletree.a: $(filter-out $(NOT_NEEDED),$(ALL_OBJS))
	$(AR) rcs $@ $^

merkle_tree_test: merkle_tree_test.o libmerkletree.a
	$(CC) $(CFLAGS) -o $@ $< -L . -lmerkletree

clean:
	rm -f $(ALL_OBJS) $(NOT_NEEDED)
	rm -f libmerkletree.a merkle_tree_test

.c.o: $<
	$(CC) $(CFLAGS) -c -o $@ $<
