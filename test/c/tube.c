#define _POSIX_C_SOURCE 199309L

#include "testlib.h"
#include "Hacl_Box.h"
#include <sodium.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include <errno.h>
#include <arpa/inet.h>
#include "FStar_IO.h"

#define secretbox_MACBYTES   16
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24


#define BLOCKSIZE            (256 * 1024)
#define CIPHERLEN(x)         (x + secretbox_MACBYTES)
#define CIPHERSIZE           CIPHERLEN(BLOCKSIZE)
#define HEADERSIZE           1024


unsigned char BOX_CHACHA_POLY = 0x00;
unsigned char SECRETBOX_CHACHA_POLY = 0x01;

uint8_t basepoint[box_SECRETKEYBYTES] = {9};

uint64_t makeStreamId() {
  uint64_t stream_id;
  randombytes_buf((uint8_t*) &stream_id, 8);
  stream_id = (stream_id & 0x00) | BOX_CHACHA_POLY;
  return stream_id;
}

bool checkStreamId(uint64_t stream_id) {
  return ((stream_id & 0xff) == 0x00);
}

void makeNonce(uint8_t* nonce, uint64_t stream_id, uint64_t timestamp, uint64_t seqno) {
  memcpy(nonce,(uint8_t*) &stream_id,8);
  memcpy(nonce+8,(uint8_t*) &timestamp,8);
  memcpy(nonce+16,(uint8_t*) &seqno,8);
}

void file_send(char* file, char* host, int port, uint8_t* skA, uint8_t* pkB, uint64_t roundup) {

  printf("Rounding up to %llu\n",roundup);

  file_handle fh;
  socket_handle conn;
  uint8_t pkA[box_PUBLICKEYBYTES];
  Hacl_EC_Curve25519_exp(pkA , basepoint, skA);


  clock_t c1, c2;
  double t1, t2;

  c1 = clock(); 

  if (file_open_read_sequential(file,&fh) == ERROR) {
    perror ("open");
    return;
  }

  uint64_t file_size = fh.status.size;
  printf("Sending file: %s, size:%llu\n",file,file_size);
  if (tcp_connect(host,port,&conn) == ERROR) {
    perror("connect");
    return;
  }

  uint8_t ciphertext[CIPHERSIZE];
  uint64_t fragments = file_size / BLOCKSIZE;
  unsigned int rem = file_size % BLOCKSIZE;
  uint64_t hrem = 0;
  if (roundup > 0 && file_size%roundup != 0) {
    hrem = (roundup - file_size%roundup);
  }
  uint64_t hsize = file_size + hrem;

  uint64_t mtime = fh.status.mtime;
  uint64_t nsize = strlen(file);
  unsigned char header[HEADERSIZE];
  memset(header,0,HEADERSIZE);
  memcpy(header,&file_size,8);
  memcpy(header+8,&mtime,8);
  memcpy(header+16,&nsize,8);
  if (strlen(file) > HEADERSIZE-24-1) {
    perror ("filename too long");
    return;
  }
  memcpy(header+24,file,nsize);

  
  uint8_t  basepoint[box_SECRETKEYBYTES] = {9};

  struct timespec spec;
  clock_gettime(CLOCK_REALTIME, &spec);
  uint64_t timestamp = spec.tv_sec;

  uint64_t stream_id = makeStreamId();

  if (tcp_write_all(&conn, (uint8_t*) &stream_id, 8) == ERROR) {
    return;
  }
  if (tcp_write_all(&conn, (uint8_t*) &timestamp, 8) == ERROR) {
    return;
  }
  if (tcp_write_all(&conn, (uint8_t*) &hsize, 8) == ERROR) {
    return;
  }
  if (tcp_write_all(&conn, pkA, box_PUBLICKEYBYTES) == ERROR) {
    return;
  }
  if (tcp_write_all(&conn, pkB, box_PUBLICKEYBYTES) == ERROR) {
    return;
  }

  uint64_t seqno = 0;
  uint8_t nonce[24];
  uint8_t key[secretbox_KEYBYTES];
  if (Hacl_Box_crypto_box_beforenm(key,pkB,skA) < 0) {
    perror("beforenm failed");
    return;
  }
  makeNonce(nonce,stream_id,timestamp,seqno);
  seqno++;
  Hacl_Box_crypto_box_easy_afternm(ciphertext, header, HEADERSIZE, nonce, key);   
  if (tcp_write_all(&conn, ciphertext, CIPHERLEN(HEADERSIZE)) == ERROR) {
    return;
  }
  
  uint64_t i;
  uint8_t* next;

  for (i = 0; i < fragments; i++) { 
    next = file_next_sequential(&fh,BLOCKSIZE);
    makeNonce(nonce,stream_id,timestamp,seqno);
    seqno++;
    Hacl_Box_crypto_box_easy_afternm(ciphertext, next, BLOCKSIZE, nonce, key);   
    if (tcp_write_all(&conn, ciphertext, CIPHERSIZE) == ERROR) {
	  return;
    }
  }

  uint8_t plaintext[BLOCKSIZE];
  memset(plaintext,0,BLOCKSIZE);
  if (rem + hrem > 0) {
    next = file_next_sequential(&fh,rem);
    memcpy(plaintext,next,rem);
    makeNonce(nonce,stream_id,timestamp,seqno);
    seqno++;
    if (hrem + rem > BLOCKSIZE) {
      rem = BLOCKSIZE;
      hrem = hrem - (BLOCKSIZE - rem);
    }
    else {
      rem = rem + hrem;
      hrem = 0;
    }
    Hacl_Box_crypto_box_easy_afternm(ciphertext, plaintext, rem, nonce, key);   
    if (tcp_write_all(&conn, ciphertext, CIPHERLEN(rem)) == ERROR) {
      return;
    }
    if (hrem > 0) {
      memset(plaintext,0,BLOCKSIZE);
      fragments = hrem / BLOCKSIZE;
      hrem = hrem % BLOCKSIZE;
      for (i = 0; i < fragments; i++){
	Hacl_Box_crypto_box_easy_afternm(ciphertext, plaintext, BLOCKSIZE, nonce, key);   
	if (tcp_write_all(&conn, ciphertext, CIPHERLEN(BLOCKSIZE)) == ERROR) {
	  return;
	}
      }
      if (hrem > 0){
	Hacl_Box_crypto_box_easy_afternm(ciphertext, plaintext, hrem, nonce, key);   
	if (tcp_write_all(&conn, ciphertext, CIPHERLEN(hrem)) == ERROR) {
	  return;
	}
	
      }
    }
  }
  tcp_close(&conn);
  c2 = clock(); 
  t2 = ((double)c2 - c1)/CLOCKS_PER_SEC;
  printf("User time for sending: %f\n", t2);

  file_close(&fh);
  return;
}

void file_recv(int port, uint8_t* pkA, uint8_t* skB) {
  file_handle fh;
  socket_handle lh,conn;
  
  uint8_t pkB[box_PUBLICKEYBYTES];
  Hacl_EC_Curve25519_exp(pkB , basepoint, skB);

  if (tcp_listen(port,&lh) == ERROR) {
    return;
  }

  while(1)
    {

      if (tcp_accept(&lh,&conn) == ERROR) {
	  return;
      }

      printf("Received connection\n");
      clock_t c1, c2;
      double t1, t2;
      c1 = clock();
      
      uint8_t ciphertext[CIPHERSIZE];
      int rb;
      uint8_t  pk1[box_PUBLICKEYBYTES], pk2[box_PUBLICKEYBYTES];
      uint64_t stream_id = 0;
      uint64_t timestamp;
      uint64_t hsize;

      if (tcp_read_all(&conn, (uint8_t *) &stream_id, 8) == ERROR) {
	perror("read did not read all connid");
	return;
      }
      //      if (checkStreamId(stream_id) == false) {
      //	perror("unexpected stream_id");
      //	return;
      //}
      if (tcp_read_all(&conn, (uint8_t *) &timestamp, 8) == ERROR) {
	perror("read did not read all timestamp");
	return;
      }
      if (tcp_read_all(&conn, (uint8_t *) &hsize, 8) == ERROR) {
	perror("read did not read ciphersize");
	return;
      }
      if (tcp_read_all(&conn, pk1, box_PUBLICKEYBYTES) == ERROR) {
	perror("read did not read all pk1");
	return;
      }
      if (tcp_read_all(&conn, pk2, box_PUBLICKEYBYTES) == ERROR) {
	perror("read did not read all pk2");
	return;
      }
      if (memcmp(pk1,pkA,box_PUBLICKEYBYTES) != 0) {
	perror("unexpected sender public key");
	return;
      }
      if (memcmp(pk2,pkB,box_PUBLICKEYBYTES) != 0) {
	perror("unexpected receiver public key");
        for (int i = 0; i < 32; i++) printf("%02x ", (unsigned char)pkB[i]);
        printf("\n");
	return;
      }
      uint8_t key[secretbox_KEYBYTES];
      if (Hacl_Box_crypto_box_beforenm(key,pkA,skB) < 0) {
	perror("beforenm failed");
	return;
      }

      uint64_t seqno = 0;
      uint8_t nonce[24];

      unsigned char header[HEADERSIZE];
      memset(header,0,HEADERSIZE);
      if (tcp_read_all(&conn, ciphertext, CIPHERLEN(HEADERSIZE)) == ERROR) {
	perror("read did not read all header");
	return;
      }
      makeNonce(nonce,stream_id,timestamp,seqno);
      seqno++;
      if (Hacl_Box_crypto_box_open_easy_afternm(header,ciphertext,CIPHERLEN(HEADERSIZE), nonce, key) != 0) {
	perror ("Header decrypt failed!");
	return;
      }

      uint64_t file_size;
      uint64_t nsize;
      uint64_t mtime;
      memcpy(&file_size,header,8);
      memcpy(&mtime,header+8,8);
      memcpy(&nsize,header+16,8);
      if (nsize > HEADERSIZE - 24 -1) {
	perror ("filename too large");
	return;
      }
      char* file;
      file = (char*) (header+24);
      printf("Receiving file: %s, size:%llu\n",file,file_size);

      if (file_open_write_sequential(file,file_size,&fh) == ERROR) {
	perror("fopen");
	return;
      }

      int fragments = file_size / BLOCKSIZE;
      int rem = file_size % BLOCKSIZE;
      uint8_t* next;

      int i;
      for (i = 0; i < fragments; i++) {
	if (tcp_read_all(&conn, ciphertext, CIPHERSIZE) == ERROR) {
	  printf("received %d fragments",i);
	  perror("read did not read all");
	  return;
	}
	next = file_next_sequential(&fh,BLOCKSIZE);

	makeNonce(nonce,stream_id,timestamp,seqno);
	seqno++;
	if (Hacl_Box_crypto_box_open_easy_afternm(next,ciphertext,CIPHERSIZE, nonce, key) != 0) {
	  perror ("decrypt failed!");
          printf("Failing fragment number: %ldth", fragments);
	  return;
	}
      }

      if (rem > 0) {
	if (tcp_read_all(&conn, ciphertext, CIPHERLEN(rem)) == ERROR) {
	  printf("received %d fragments",i);
	  perror("read did not read all");
	  return;
	}
	next = file_next_sequential(&fh,rem);
	makeNonce(nonce,stream_id,timestamp,seqno);
	seqno++;
	if (Hacl_Box_crypto_box_open_easy_afternm(next,ciphertext,CIPHERLEN(rem), nonce, key) != 0) {
	  perror ("decrypt failed last!");
	  return;
	}
      }
      if (file_close (&fh) == ERROR) {
	perror ("close fh");
	return;
      }
      if (tcp_close (&conn) == ERROR) {
	perror ("close sockfd");
	return;
      }
      c2 = clock();
      t1 = ((double)c2 - c1)/CLOCKS_PER_SEC;
      printf("User time for receiving: %f\n", t1);

    }
  return;
}


void print_usage() {
  printf("Usage: tube send file host port\n       tube receive port\n       tube keygen\nOptions:\n-k --myprivatekey <64 hex characters>\n-p --peerpublickey <64 hex characters>\n-h --hidesize <number>K | <number>M | <number>G\n");
}

void readHexLine(uint8_t* str, int len) {
  unsigned int x;
  int res;
  for (int i = 0; i < len; i++) {
    res = scanf("%02x",&x);
    str[i] = (uint8_t) x;
  }
}

void sreadHexLine(char* a, uint8_t* str, int len) {
  unsigned int x;
  for (int i = 0; i < len; i++) {
    sscanf(a+(2*i),"%02x",&x);
    str[i] = (uint8_t) x;
  }
}

void printHexLine(uint8_t* str, int len) {
  for (int i = 0; i < len; i++)
    printf("%02x",(unsigned int) str[i]);
  printf("\n");
}

static struct option long_options[] =
  {
    /* These options set a flag. */
    {"myprivatekey", required_argument, 0, 'k'},
    {"peerpublickey", required_argument, 0, 'p'},
    {"hidesize",   required_argument, 0, 'h'},
    {0, 0, 0, 0}
  };

int main(int argc, char *argv[]){
  uint8_t sk[secretbox_KEYBYTES];
  uint8_t pk[box_PUBLICKEYBYTES];
  unsigned int port;
  char host[512];
  char file[512];
  uint64_t roundup = 0;
  bool got_sk = false, got_pk = false;
  unsigned int n = 0;
  unsigned char u = 0;
  
  if (argc == 2 && strcmp(argv[1], "keygen") == 0) {
    crypto_box_keypair(pk,sk);
    printf("Your Curve25519 secret key (64 hex characters): ");
    printHexLine(sk,secretbox_KEYBYTES);
    printf("Your Curve25519 public key (64 hex characters): ");
    printHexLine(pk,box_PUBLICKEYBYTES);
    return EXIT_SUCCESS;;
  } 
  
  while (1)
    {
      int option_index = 0;
      
      char c = getopt_long (argc, argv, "k:p:h:",
		       long_options, &option_index);
      if (c == -1)
	break;
      switch (c)
	{
	case 'k':
	  sreadHexLine(optarg,sk,secretbox_KEYBYTES);
	  got_sk = true;
	  break;
	case 'p':
	  sreadHexLine(optarg,pk,box_PUBLICKEYBYTES);
	  got_pk = true;
	  break;
	case 'h':
	  sscanf(optarg,"%u%c",&n,&u);
	  switch (u) {
	  case 'K': roundup = n * 1024; break;
	  case 'M': roundup = n * 1024 * 1024; break;
	  case 'G': roundup = n * 1024 * 1024 * 1024; break;
	  default: printf("Hiding size up to %u%c",n,u); print_usage(); abort(); 
	  } 
	  break;
	default:
	  print_usage();
	  fflush(stdout);
	  abort();
	}
    }
  if (!got_sk) {
    printf("Your Curve25519 secret key (64 hex characters): ");
    readHexLine(sk,secretbox_KEYBYTES);
  }
  if (!got_pk) {
    printf("Peer Curve25519 public key (64 hex characters): ");
    readHexLine(pk,box_PUBLICKEYBYTES);
  }
  
  if (argc - optind == 3 && strcmp(argv[optind], "send") == 0) {
      strcpy(file, argv[optind+1]);
      sscanf(argv[optind+2],"%512[^:]:%u",host,&port);
      file_send(file,host,port,sk,pk,roundup);
  } else if (argc - optind == 2 && strcmp(argv[optind], "receive") == 0) {
      sscanf(argv[optind+1],"%u",&port);
      file_recv(port,pk,sk);
  } else {
    print_usage();
    abort();
  }

  return EXIT_SUCCESS;
}
