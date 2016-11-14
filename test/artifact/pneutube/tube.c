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
#include "Hacl_Tube.h"

#define secretbox_MACBYTES   16
#define secretbox_NONCEBYTES 24
#define secretbox_KEYBYTES   32
#define box_MACBYTES         16
#define box_PUBLICKEYBYTES   32
#define box_SECRETKEYBYTES   32
#define box_NONCEBYTES       24

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
  printf("Hiding size up to %u%c\n", n, u);
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
      Hacl_Tube_file_send(strlen(file),file,roundup,host,port,sk,pk);
  } else if (argc - optind == 2 && strcmp(argv[optind], "receive") == 0) {
      sscanf(argv[optind+1],"%u",&port);
      Hacl_Tube_file_recv(port,pk,sk);
  } else {
    print_usage();
    abort();
  }

  return EXIT_SUCCESS;
}
