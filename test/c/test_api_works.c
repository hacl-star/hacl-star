#include "testlib.h"
#include "Hacl_Box.h"
#include <sodium.h>
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
#include <stdlib.h>
#include <errno.h>
#include <arpa/inet.h> 

#define MESSAGE_LEN 44
#define secretbox_MACBYTES   16
#define CIPHERTEXT_LEN (secretbox_MACBYTES + MESSAGE_LEN)
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24

uint8_t *msg = (uint8_t*) "testtesttesttesttesttesttesttesttesttesttest";

uint8_t nonce[secretbox_NONCEBYTES] = {
  0x00, 0x01, 0x02, 0x03,
  0x04, 0x05, 0x06, 0x07,
  0x08, 0x09, 0x10, 0x11,
  0x12, 0x13, 0x14, 0x15,
  0x16, 0x17, 0x18, 0x19,
  0x20, 0x21, 0x22, 0x23,
};

uint8_t key[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1b
};

uint8_t sk1[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

uint8_t sk2[secretbox_KEYBYTES] = {
  0x85, 0xd6, 0xbe, 0x78,
  0x57, 0x55, 0x6d, 0x33,
  0x7f, 0x44, 0x52, 0xfe,
  0x42, 0xd5, 0x06, 0xa8,
  0x01, 0x03, 0x80, 0x8a,
  0xfb, 0x0d, 0xb2, 0xfd,
  0x4a, 0xbf, 0xf6, 0xaf,
  0x41, 0x49, 0xf5, 0x1c
};

void test_correctness() {
  if (sodium_init() == -1) {
    exit(EXIT_FAILURE);
  }
  uint8_t ciphertext[CIPHERTEXT_LEN], ciphertext2[CIPHERTEXT_LEN],
    mac[16],mac2[16],
    decrypted[MESSAGE_LEN], decrypted2[MESSAGE_LEN],
    pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES],
    test[32], test2[32],
    basepoint[box_SECRETKEYBYTES] = {9};
  uint32_t res;
  int i;
  /* Testing the secret box primitives */  
  Hacl_SecretBox_crypto_secretbox_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, key);
  res = crypto_secretbox_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, key);

  printf("SecretBox decryption with libsodium was a %s.\n", res == 0 ? "success" : "failure");
  TestLib_compare_and_print("Secret box", msg, decrypted, MESSAGE_LEN);

  for(i = 0; i < MESSAGE_LEN; i++) decrypted[i] = 0;
  for(i = 0; i < CIPHERTEXT_LEN; i++) ciphertext[i] = 0;

  // Creating public/private key couples
  Hacl_EC_Curve25519_exp(pk1 , basepoint, sk1);
  Hacl_EC_Curve25519_exp(pk2, basepoint, sk2);

  /* Testing the box primitives */
  i = crypto_box_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, pk1, sk2);  
  res = Hacl_Box_crypto_box_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, pk2, sk1);
  printf("Box decryption with libsodium was a %s.\n", res == 0 ? "success" : "failure");
  
  TestLib_compare_and_print("Box", msg, decrypted, MESSAGE_LEN);
}

#define SIZE (512*1024*1024)

void test_perf1() {
  void *plain = malloc(SIZE), *cipher = malloc(SIZE);
  uint8_t mac[16];
  clock_t c1, c2;
  double t1, t2;

  c1 = clock();
  crypto_secretbox_detached(cipher, mac, plain, SIZE, nonce, key);
  c2 = clock();
  t2 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for Sodium: %f\n", t2);

  c1 = clock();
  Hacl_SecretBox_crypto_secretbox_detached(cipher, mac, plain, SIZE, nonce, key);
  c2 = clock();
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for HACL: %f\n", t1);


  printf("Slowdown (AEAD): %f\n", t1/t2);
}

void test_perf2() {
  void *plain = malloc(SIZE);
  uint8_t mac[16], mac2[16], mac3[16];
  clock_t c1, c2;
  double t1, t2, t3;

  c1 = clock();
  crypto_onetimeauth(mac3, plain, SIZE, key);
  c2 = clock();
  t2 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for Sodium: %f\n", t2);

  c1 = clock();
  Hacl_Symmetric_Poly1305_64_crypto_onetimeauth(mac, plain, SIZE, key);
  c2 = clock();
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for HACL 64bit: %f\n", t1);
  
  c1 = clock();
  Hacl_Symmetric_Poly1305_poly1305_mac(mac2, plain, SIZE, key);
  c2 = clock();
  t3 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for HACL 32bit: %f\n", t3);

  printf("Slowdown (Poly1305-32): %f\n", t3/t2);
  printf("Slowdown (Poly1305-64): %f\n", t1/t2);
  TestLib_compare_and_print("1Gb Poly1305", mac3, mac, 16);
}

void test_perf3() {
  void *plain = malloc(SIZE), *cipher = malloc(SIZE);
  uint8_t mac[16];
  clock_t c1, c2;
  double t1, t2;

  c1 = clock();
  Hacl_Symmetric_HSalsa20_crypto_stream_xsalsa20_xor(cipher, plain, SIZE, nonce, key);
  c2 = clock();
  t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for HACL: %f\n", t1);

  c1 = clock();
  crypto_stream_xsalsa20_xor(cipher, plain, SIZE, nonce, key);
  c2 = clock();
  t2 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for Sodium: %f\n", t2);

  printf("Slowdown (XSalsa20): %f\n", t1/t2);
}

void test_file_send(char* file) {
  struct stat sb;
  off_t len;
  unsigned char *p;
  int fd;


  fd = open (file, O_RDONLY);
  if (fd == -1) {
    perror ("open");
    return;
  }

  if (fstat (fd, &sb) == -1) {
    perror ("fstat");
    return;
  }

  if (!S_ISREG (sb.st_mode)) {
    fprintf (stderr, "%s is not a filen", file);
    return;
  }

  uint64_t file_size = sb.st_size;
  printf("file: %s, size:%lld\n",file,file_size);
  p = mmap (0, file_size, PROT_READ, MAP_SHARED, fd, 0);
  if (p == MAP_FAILED) {
    perror ("mmap");
    return; 
  }


  int adv = madvise(p,file_size,MADV_SEQUENTIAL|MADV_WILLNEED);

  if (close (fd) == -1) {
    perror ("close");
    return; 
  }

  int sockfd = 0, n = 0;
  struct sockaddr_in serv_addr; 
  if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      printf("\n Error : Could not create socket \n");
      return;
    } 

  memset(&serv_addr, '0', sizeof(serv_addr)); 
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_port = htons(5000); 
  if(inet_pton(AF_INET, "127.0.0.1", &serv_addr.sin_addr)<=0)
    {
      printf("\n inet_pton error occured\n");
      return;
    } 
  if( connect(sockfd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0)
    {
      printf("\n Error : Connect Failed \n");
      return;
    } 

  int block = 4096;
  int cipher_len = block + secretbox_MACBYTES;
  uint8_t ciphertext[cipher_len];
  uint8_t plaintext[block];
  int fragments = file_size / block;
  int rem = file_size % block;
  int written;


  int header_size = 1024;
  uint64_t mtime = sb.st_mtime;
  uint64_t nsize = strlen(file);
  unsigned char header[header_size];
  memset(header,0,header_size);
  memcpy(header,&file_size,8);
  memcpy(header+8,&mtime,8);
  memcpy(header+16,&nsize,8);
  if (strlen(file) > header_size-24) {
    perror ("filename too long");
    return;
  }
  memcpy(header+24,file,nsize);

  
  uint8_t basepoint[box_SECRETKEYBYTES] = {9};
  uint8_t  pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES];
  uint64_t connection_id = 0;
  Hacl_EC_Curve25519_exp(pk1 , basepoint, sk1);
  Hacl_EC_Curve25519_exp(pk2 , basepoint, sk2);
  if (write(sockfd, &connection_id, 8) < 8) {
    perror("write did not write all");
    return;
  }
  if (write(sockfd, pk1, box_PUBLICKEYBYTES) < box_PUBLICKEYBYTES) {
    perror("write did not write all");
    return;
  }
  if (write(sockfd, pk2, box_PUBLICKEYBYTES) < box_PUBLICKEYBYTES) {
    perror("write did not write all");
    return;
  }

  /* Testing the box primitives */
  //  i = crypto_box_detached(ciphertext, mac, msg, MESSAGE_LEN, nonce, pk1, sk2);  
  //res = Hacl_Box_crypto_box_open_detached(decrypted, ciphertext, mac, MESSAGE_LEN, nonce, pk2, sk1);
  //printf("Box decryption with libsodium was a %s.\n", res == 0 ? "success" : "failure");

  crypto_secretbox_easy(ciphertext, header, header_size, nonce, key);   
  //if (crypto_secretbox_open_easy(plaintext,ciphertext,cipher_len, nonce, key) != 0) {
  //  perror ("decrypt failed!");
  //return;
  //}
  //fwrite(plaintext,1,block,stdout);
  //fflush(stdout);
  if (write(sockfd, ciphertext, header_size + secretbox_MACBYTES) < header_size + secretbox_MACBYTES) {
    perror("write did not write all");
    return;
  }
  
  int i;
  for (i = 0; i < fragments; i++) {
    crypto_secretbox_easy(ciphertext, p + (i * block), block, nonce, key);   
    //if (crypto_secretbox_open_easy(plaintext,ciphertext,cipher_len, nonce, key) != 0) {
    //  perror ("decrypt failed!");
    //return;
    //}
    //fwrite(plaintext,1,block,stdout);
    //fflush(stdout);
    if (write(sockfd, ciphertext, cipher_len) < cipher_len) {
      perror("write did not write all");
	  return;
    }
  }

  crypto_secretbox_easy(ciphertext, p + (i * block), rem, nonce, key);   
  //if (crypto_secretbox_open_easy(plaintext,ciphertext,rem + secretbox_MACBYTES, nonce, key) != 0) {
  //  perror ("decrypt failed!");
  //  return;
  //}
  //fwrite(plaintext,1,rem,stdout);
  //fflush(stdout);
  if (write(sockfd, ciphertext, rem+secretbox_MACBYTES)  < rem+secretbox_MACBYTES) {
    perror("write did not write all");
    return;
  }
  shutdown(sockfd,2);

  if (madvise(p, file_size, MADV_DONTNEED) == -1) {
    perror ("madvise");
    return; 
  }
  if (munmap (p, file_size) == -1) {
    perror ("munmap");
    return; 
  }
  return;
}

int read_all(int fd, uint8_t* buf, int buf_len) {
  int got = 0;
  while (got < buf_len) {
    int n = read(fd, buf+got, buf_len-got);
    if (n < 0) return (-1);
    got += n;
  }
  return 0;
}
void test_file_recv() {
  struct stat sb;
  off_t len;
  unsigned char *p;
  int fd;
  FILE *fp;

  int sockfd = 0, listenfd = 0;
  struct sockaddr_in serv_addr; 
  if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      printf("\n Error : Could not create socket \n");
      return;
    } 
  if((listenfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      printf("\n Error : Could not create socket \n");
      return;
    } 
  memset(&serv_addr, '0', sizeof(serv_addr)); 
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_addr.s_addr = htonl(INADDR_ANY);
  serv_addr.sin_port = htons(5000); 

  if (bind(listenfd, (struct sockaddr*)&serv_addr, sizeof(serv_addr)) < 0) {
    perror("bind");
    return;
  }
    
  if (listen(listenfd, 10) < 0) {
    perror("listen");
    return;
  }
  while(1)
    {

      sockfd = accept(listenfd, (struct sockaddr*)NULL, NULL); 
      if( sockfd < 0)
	{
	  printf("\n Error : accept Failed \n");
	  return;
	} 
      
      int block = 4096;
      int cipher_len = block + secretbox_MACBYTES;
      uint8_t ciphertext[cipher_len];
      uint8_t plaintext[block];
      int rb;
      
      uint8_t  pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES];
      uint64_t connection_id = 0;
      if (read_all(sockfd, (uint8_t *) &connection_id, 8) < 0) {
	perror("read did not read all header");
	return;
      }
      if (read_all(sockfd, pk1, box_PUBLICKEYBYTES) < 0) {
	perror("read did not read all header");
	return;
      }
      if (read_all(sockfd, pk2, box_PUBLICKEYBYTES) < 0) {
	perror("read did not read all header");
	return;
      }

      int header_size = 1024;
      unsigned char header[header_size];
      memset(header,0,header_size);
      if (read_all(sockfd, ciphertext, header_size + secretbox_MACBYTES) < 0) {
	perror("read did not read all header");
	return;
      }
      if (crypto_secretbox_open_easy(header,ciphertext,header_size + secretbox_MACBYTES, nonce, key) != 0) {
	perror ("decrypt failed!");
	return;
      }

      uint64_t file_size;
      uint64_t nsize;
      uint64_t mtime;
      memcpy(&file_size,header,8);
      memcpy(&mtime,header+8,8);
      memcpy(&nsize,header+16,8);
      if (nsize > block - 24) {
	perror ("filename too large");
	return;
      }
      char* file;
      file = header+24;
      printf("file: %s, nsize: %lld, size:%lld\n",file,nsize,file_size);

      fd = open (file, O_RDWR | O_CREAT | O_TRUNC, (mode_t) 0600);
      if (fd == -1) {
	perror ("open");
	return;
      }
      
      if (fstat (fd, &sb) == -1) {
	perror ("fstat");
	return;
      }
      
      if (!S_ISREG (sb.st_mode)) {
	fprintf (stderr, "%s is not a filen", file);
	return;
      }
      fsync(fd);
      fp = fdopen(fd,"w+");

      ftruncate(fd,file_size);

      int fragments = file_size / block;
      int rem = file_size % block;


      int i;
      for (i = 0; i < fragments; i++) {
	if (read_all(sockfd, ciphertext, cipher_len) < 0) {
	  printf("received %d fragments",i);
	  perror("read did not read all");
	  return;
	}
	
	if (crypto_secretbox_open_easy(plaintext,ciphertext,cipher_len, nonce, key) != 0) {
	  perror ("decrypt failed!");
	  return;
	}
	fwrite(plaintext,block,1,fp);
	//fwrite(plaintext,block,1,stdout);
	//fflush(stdout);
      }

      if (read_all(sockfd, ciphertext, rem + secretbox_MACBYTES) < 0) {
        printf("received %d fragments",i);
	perror("read did not read all");
	  return;
      }
      memset(plaintext,0,block);
      if (crypto_secretbox_open_easy(plaintext,ciphertext,rem + secretbox_MACBYTES, nonce, key) != 0) {
	perror ("decrypt failed last!");
	  return;
      }
      fwrite(plaintext,rem,1,fp);
      //fwrite(plaintext,rem,1,stdout);
      //fflush(stdout);
      fflush(fp);
      
      if (fclose (fp) == -1) {
	perror ("close fp");
	return; 
      }
      if (close (sockfd) == -1) {
	perror ("close sockfd");
	return; 
      }
    }
  return;
}


int main(int argc, char *argv[]){
  if (argc == 2 && strcmp(argv[1], "perf1") == 0) {
    test_perf1();
  } else if (argc == 2 && strcmp(argv[1], "perf2") == 0) {
    test_perf2();
  } else if (argc == 2 && strcmp(argv[1], "perf3") == 0) {
    test_perf3();
  } else if (argc == 3 && strcmp(argv[1], "send") == 0) {
    test_file_send(argv[2]);
  } else if (argc == 2 && strcmp(argv[1], "receive") == 0) {
    test_file_recv();
  } else {
    test_correctness();
  }

  return EXIT_SUCCESS;
}
