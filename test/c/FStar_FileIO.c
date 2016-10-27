#include "FStar_IO.h"

result file_open_read_sequential(char* file,file_handle* fh){
  struct stat sb;
  unsigned char *p;
  int fd;
  

  fd = open (file, O_RDONLY);
  if (fd == -1) {
    perror ("open");
    return ERROR;
  }

  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return ERROR;
  }

  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a filen", file);
    return ERROR;
  }

  uint64_t file_size = sb.st_size;

  p = mmap (0, file_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (p == MAP_FAILED) {
    perror ("mmap");
    return ERROR; 
  }

  int adv = madvise(p,file_size,MADV_SEQUENTIAL|MADV_WILLNEED);

  if (close (fd) == -1) {
    perror ("close");
    return ERROR; 
  }

  fh->status.mtime = sb.st_mtime;
  fh->status.size = sb.st_size;
  fh->buf = p;
  fh->current = 0;
  return OK;
}


result file_open_write_sequential(char* file,uint64_t file_size,file_handle* fh){
  struct stat sb;
  off_t len;
  unsigned char *p;
  int fd,i;
  
  fd = open (file, O_RDWR | O_CREAT | O_TRUNC, (mode_t) 0600);
  if (fd == -1) {
    perror ("open");
    return ERROR;
  }
  
  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return ERROR;
  }
  
  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a filen", file);
    return ERROR;
  }
  i = ftruncate(fd,file_size);
  fsync(fd); 
  p = mmap (0, file_size, PROT_WRITE, MAP_PRIVATE, fd, 0);
  if (p == MAP_FAILED) {
    perror ("mmap");
    return ERROR; 
  }

  int adv = madvise(p,file_size,MADV_SEQUENTIAL|MADV_WILLNEED);

  if (close (fd) == -1) {
    perror ("close");
    return ERROR; 
  }

  fh->status.mtime = sb.st_mtime;
  fh->status.size = file_size;
  fh->buf = p;
  fh->current = 0;

  return OK;
}

uint8_t* file_next_sequential(file_handle* fh,uint64_t len) {
  int curr = fh->current;
  fh->current += len;
  return (fh->buf + curr);
}

result file_close(file_handle* fh) {
  if (madvise(fh->buf, fh->status.size, MADV_DONTNEED) == -1) {
    perror ("madvise");
    return ERROR; 
  }
  if (munmap (fh->buf, fh->status.size) == -1) {
    perror ("munmap");
    return ERROR; 
  }
  return OK;
}
