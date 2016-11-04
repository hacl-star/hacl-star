#ifndef FSTAR_IO
#define FSTAR_IO
//#define _POSIX_C_SOURCE 199309L
//#define _BSD_SOURCE
//#define _DEFAULT_SOURCE
//#define _GNU_SOURCE

#include <time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <strings.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>
#include <arpa/inet.h> 
#include "testlib.h"

typedef enum {FileOk, FileError} fresult;
typedef enum {FileOpen, FileClosed} fd_state;


/* Same as the FileIO.Types type declarations */
typedef struct PaddedFileIO_mmap {
  uint64_t current;
  uint8_t* buf;
} PaddedFileIO_mmap;

typedef struct file_descriptor {
  int fd;
  uint64_t current;
  uint8_t* mmap;
  uint8_t* last;
} file_descriptor;

typedef struct file_stat {
  uint8_t* name;
  uint64_t mtime;
  uint64_t size;
} file_stat;

typedef struct file_handle {
  file_stat stat;
  file_descriptor fd;
} file_handle;


#define PaddedFileIO_max_block_size (256 * 1024)


fresult PaddedFileIO_file_open_read_sequential(uint8_t* file, file_handle* fh);
fresult PaddedFileIO_file_open_write_sequential(file_stat st, file_handle* fh);
uint8_t* PaddedFileIO_file_next_read_buffer(file_handle* fh,uint64_t len);
uint8_t* PaddedFileIO_file_next_write_buffer(file_handle* fh,uint64_t len);
fresult PaddedFileIO_file_close(file_handle* fh);


typedef enum {SocketOk, SocketError} sresult;

typedef struct io_socket {
  int fd;
  uint64_t sent_bytes;
  uint64_t received_bytes;
} io_socket;


sresult SocketIO_tcp_connect(char* host, int port, io_socket* sh);
sresult SocketIO_tcp_listen(int port, io_socket* sh);
sresult SocketIO_tcp_accept(io_socket* lh, io_socket* conn);
sresult SocketIO_tcp_write_all(io_socket* conn, uint8_t* buf, uint64_t len);
sresult SocketIO_tcp_read_all(io_socket* conn, uint8_t* buf, int len);
sresult SocketIO_tcp_close(io_socket* conn);

/* file_handle PaddedFileIO_init_file_handle(); */
/* io_socket   SocketIO_init_socket(); */
extern file_handle PaddedFileIO_init_file_handle;
extern io_socket   SocketIO_init_socket;


/* typedef struct { */
/*   PaddedFileIO_fresult r; */
/*   uint8_t* streamID; */
/*   PaddedFileIO_file_stat fs; */
/* } Hacl_Tube_open_result; */

/* Hacl_Tube_open_result Hacl_Tube_file_send(uint8_t* file, uint64_t roundup, uint8_t* host, uint32_t port, uint8_t* skA, uint8_t* pkB); */
/* Hacl_Tube_open_result Hacl_Tube_file_recv(uint32_t port, uint8_t* pkA, uint8_t* skB); */
#endif
