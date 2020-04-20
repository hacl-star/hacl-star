# Just for CI

SOURCES = $(wildcard *.c)
CFLAGS += -I../../kremlin/include
CFLAGS += -I../../kremlin/kremlib/dist/minimal
CFLAGS += -D'C_String_print(X)=printf(X)'
CFLAGS += -D'LowStar_Printf_print_string(X)=printf(X)'
CFLAGS += -D'LowStar_Printf_print_u32(X)=printf("%"PRIu32, X)'
CFLAGS += -D'LowStar_Printf_print_lmbuffer_u8(X, Y)=for (size_t i = 0; i < X; ++i) printf("%"PRIu8, (Y)[i])'

SED=$(shell which gsed && echo gsed || echo sed)

hack:
	$(SED) -i 's/extern void LowStar_Printf_.*//g' *.c
	$(SED) -i 's/extern void C_String_printf.*//g' *.c

all: $(patsubst %.c,%.test,$(SOURCES))

%.exe: %.o ../../gcc-compatible/libevercrypt.a
	$(CC) $(CFLAGS) $^ -o $@

.PHONY: .test
%.test: %.exe
	./$<
