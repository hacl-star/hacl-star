#ifndef PADDED_FILE_IO_IMPL
#define PADDED_FILE_IO_IMPL

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
#include "FileIO_Types.h"

/* FileIO_Types_file_handle PaddedFileIO_init_file_handle ={ {NULL, 0, 0}, {0, 0, NULL, NULL} }; */

// should not be necessary thanks to inlining
#define PaddedFileIO_max_block_size (256 * 1024)

FileIO_Types_fresult PaddedFileIO_file_open_read_sequential(uint8_t* file,FileIO_Types_file_handle* fh){
  struct stat sb;
  unsigned char *p;
  int fd;
  

  fd = open ((char*) file, O_RDONLY);
  if (fd == -1) {
    perror ("open");
    return FileIO_Types_fresult_FileError;
  }

  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return FileIO_Types_fresult_FileError;
  }

  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a filen", file);
    return FileIO_Types_fresult_FileError;
  }

  uint64_t file_size = sb.st_size;

  p = mmap (0, file_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (p == MAP_FAILED) {
    perror ("mmap");
    return FileIO_Types_fresult_FileError; 
  }

  int adv = madvise(p,file_size,MADV_SEQUENTIAL|MADV_WILLNEED);

  fh->stat.mtime = sb.st_mtime;
  fh->stat.size = sb.st_size;
  fh->stat.name = file;
  fh->fd.fd_fd = fd;
  fh->fd.mmap = p;
  fh->fd.last = (uint8_t*) malloc(PaddedFileIO_max_block_size);
  memset(fh->fd.last,0,PaddedFileIO_max_block_size);
  fh->fd.current = 0;
  return FileIO_Types_fresult_FileOk;
}


FileIO_Types_fresult PaddedFileIO_file_open_write_sequential(FileIO_Types_file_stat st, FileIO_Types_file_handle* fh){
  struct stat sb;
  off_t len;
  unsigned char *p;
  int fd,i;
  
  fd = open ((char*) st.name, O_RDWR | O_CREAT | O_TRUNC, (mode_t) 0600);
  if (fd == -1) {
    perror ("open");
    return FileIO_Types_fresult_FileError;
  }
  
  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return FileIO_Types_fresult_FileError;
  }
  
  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a filen", st.name);
    return FileIO_Types_fresult_FileError;
  }
  i = ftruncate(fd,st.size + PaddedFileIO_max_block_size);
  fsync(fd); 
  p = mmap (0, st.size + PaddedFileIO_max_block_size, PROT_WRITE, MAP_SHARED, fd, 0);
  if (p == MAP_FAILED) {
    perror ("mmap");
    return FileIO_Types_fresult_FileError; 
  }

  int adv = madvise(p,st.size + PaddedFileIO_max_block_size,MADV_SEQUENTIAL|MADV_WILLNEED);

  fh->stat = st;
 
  fh->fd.fd_fd = fd;
  fh->fd.mmap = p;
  fh->fd.last = (uint8_t*) malloc(PaddedFileIO_max_block_size);
  memset(fh->fd.last,0,PaddedFileIO_max_block_size);
  fh->fd.current = 0;

  return FileIO_Types_fresult_FileOk;
}

uint8_t* PaddedFileIO_file_next_read_buffer(FileIO_Types_file_handle* fh,uint64_t len) {
  if (len > PaddedFileIO_max_block_size) {
    perror("read_buf: len > max_block_size!\n");
    abort();
  }
  int curr = fh->fd.current;
  fh->fd.current += len;
  if (curr + len <= fh->stat.size) {
   return (fh->fd.mmap + curr);
  }
  else if (curr <= fh->stat.size && curr + len > fh->stat.size) {
    memset(fh->fd.last,0, PaddedFileIO_max_block_size);
    memcpy(fh->fd.last,fh->fd.mmap + curr, fh->stat.size - curr);
    return (fh->fd.last);
  }
  memset(fh->fd.last,0, PaddedFileIO_max_block_size);
  return (fh->fd.last);
}

uint8_t* PaddedFileIO_file_next_write_buffer(FileIO_Types_file_handle* fh,uint64_t len) {
  int curr = fh->fd.current;
  if (len > PaddedFileIO_max_block_size) {
    perror("write_buf: len > max_block_size!\n");
    abort();
  }
  if (curr + len <= fh->stat.size + PaddedFileIO_max_block_size) {
    fh->fd.current += len;
    return (fh->fd.mmap + curr);
  }
  memset(fh->fd.last,0,PaddedFileIO_max_block_size);
  return (fh->fd.last);
}

FileIO_Types_fresult PaddedFileIO_file_close(FileIO_Types_file_handle* fh) {
  int tmp;
  tmp = ftruncate(fh->fd.fd_fd,fh->stat.size);
  free(fh->fd.last);
  if (close (fh->fd.fd_fd) == -1) {
    perror ("close");
    return FileIO_Types_fresult_FileError; 
  }

  if (madvise(fh->fd.mmap, fh->stat.size, MADV_DONTNEED) == -1) {
    perror ("madvise");
    return FileIO_Types_fresult_FileError; 
  }
  if (munmap (fh->fd.mmap, fh->stat.size) == -1) {
    perror ("munmap");
    return FileIO_Types_fresult_FileError; 
  }
  return FileIO_Types_fresult_FileOk;
}

#endif
