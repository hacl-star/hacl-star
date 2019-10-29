CFLAGS = -O3 -std=gnu11 -Wall -Wextra -march=native

all: rng.o aes/aes.o aes/aes_c.o

%.o: %.c
	$(CC) -c $(CFLAGS) $< -o $@
