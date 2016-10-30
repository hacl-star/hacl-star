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

typedef enum {FileOk, FileError} PaddedFileIO_fresult;
typedef enum {FileOpen, FileClosed} PaddedFileIO_fd_state;

typedef struct {
  uint64_t current;
  uint8_t* buf;
} PaddedFileIO_mmap;

typedef struct {
  int fd;
  uint64_t current;
  uint8_t* mmap;
  uint8_t* last;
} PaddedFileIO_file_descriptor;

typedef struct {
  uint8_t* name;
  uint64_t mtime;
  uint64_t size;
} PaddedFileIO_file_stat;

typedef struct {
  PaddedFileIO_file_stat stat;
  PaddedFileIO_file_descriptor fd;
} PaddedFileIO_file_handle;


#define PaddedFileIO_max_block_size (256 * 1024)

PaddedFileIO_fresult PaddedFileIO_file_open_read_sequential(uint8_t* file, PaddedFileIO_file_handle* fh);
PaddedFileIO_fresult PaddedFileIO_file_open_write_sequential(PaddedFileIO_file_stat st, PaddedFileIO_file_handle* fh);
uint8_t* PaddedFileIO_file_next_read_buffer(PaddedFileIO_file_handle* fh,uint64_t len);
uint8_t* PaddedFileIO_file_next_write_buffer(PaddedFileIO_file_handle* fh,uint64_t len);
PaddedFileIO_fresult PaddedFileIO_file_close(PaddedFileIO_file_handle* fh);


typedef enum {SocketOk, SocketError} SocketIO_sresult;

typedef struct {
  int fd;
  uint64_t sent_bytes;
  uint64_t received_bytes;
} SocketIO_socket;


SocketIO_sresult SocketIO_tcp_connect(char* host, int port, SocketIO_socket* sh);
SocketIO_sresult SocketIO_tcp_listen(int port, SocketIO_socket* sh);
SocketIO_sresult SocketIO_tcp_accept(SocketIO_socket* lh, SocketIO_socket* conn);
SocketIO_sresult SocketIO_tcp_write_all(SocketIO_socket* conn, uint8_t* buf, uint64_t len);
SocketIO_sresult SocketIO_tcp_read_all(SocketIO_socket* conn, uint8_t* buf, int len);
SocketIO_sresult SocketIO_tcp_close(SocketIO_socket* conn);

typedef struct {
  PaddedFileIO_fresult r;
  uint8_t* streamID;
  PaddedFileIO_file_stat fs;
} Hacl_Tube_open_result;

Hacl_Tube_open_result Hacl_Tube_file_send(uint8_t* file, uint64_t roundup, uint8_t* host, uint32_t port, uint8_t* skA, uint8_t* pkB);
Hacl_Tube_open_result Hacl_Tube_file_recv(uint32_t port, uint8_t* pkA, uint8_t* skB);
#endif
