
all: libmerkletree.a

CFLAGS+=-I kremlin/include -I kremlin/kremlib -I evercrypt/include 

THIS_SOURCE=$(wildcard *.c)
EVERCRYPT_SRC=$(wildcard evercrypt/extracted/*.c)
KREMLIB_SRC=$(wildcard kremlin/kremlib/extracted/*.c)
ALL_OBJS=$(patsubst %.c,%.o,$(THIS_SOURCE) $(EVERCRYPT_SRC) $(KREMLIB_SRC))
NOT_NEEDED=kremlin/kremlib/extracted/FStar_UInt128.o

libmerkletree.a: $(filter-out $(NOT_NEEDED),$(ALL_OBJS))
	$(AR) rcs $@ $^

merkle_tree_test: merkle_tree_test.o
	$(CC) $(CFLAGS) -static -L . -lmerkletree -o $@ $<

clean:
	rm -f $(ALL_OBJS)
	rm -f libmerkletree.a merkle_tree_test

.c.o: $<
	$(CC) $(CFLAGS) -c -o $@ $<
