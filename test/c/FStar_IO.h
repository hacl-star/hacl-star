#define _POSIX_C_SOURCE 199309L
#define _BSD_SOURCE

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <strings.h>

#define h_addr h_addr_list[0]

typedef enum {OK, ERROR} result;

typedef struct {
  uint64_t mtime;
  uint64_t size;
} file_status;

typedef struct {
  file_status status;
  uint8_t* buf;
  uint64_t current;
} file_handle;

typedef struct {
  int fd;
  uint64_t sent_bytes;
  uint64_t received_bytes;
} socket_handle;

result file_open_read_sequential(char* file, file_handle* fh);
result file_open_write_sequential(char* file,uint64_t file_size,file_handle* fh);
uint8_t* file_next_sequential(file_handle* fh,uint64_t len);
result file_close(file_handle* fh);

result tcp_connect(char* host, int port, socket_handle* sh);
result tcp_listen(int port, socket_handle* sh);
result tcp_accept(socket_handle* lh, socket_handle* conn);
result tcp_write_all(socket_handle* conn, uint8_t* buf, uint64_t len);
result tcp_read_all(socket_handle* conn, uint8_t* buf, int len);
result tcp_close(socket_handle* conn);
