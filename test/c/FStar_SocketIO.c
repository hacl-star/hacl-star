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
#include "FStar_IO.h"

result tcp_connect(char* host, int port, socket_handle* sh) {
  int sockfd = 0, n = 0;
  struct sockaddr_in serv_addr; 
  if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      perror("Error : Could not create socket");
      return ERROR;
    } 

  struct hostent *server = gethostbyname(host);
  if (server == NULL) {
    perror("ERROR, DNS lookup on host failed");
    return ERROR;
  }
  memset(&serv_addr, '0', sizeof(serv_addr)); 
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_port = htons(port); 
  bcopy((char *)server->h_addr, 
	(char *)&serv_addr.sin_addr.s_addr, server->h_length);
  /*
  if(inet_pton(AF_INET, host, &serv_addr.sin_addr)<=0)
    {
      perror("inet_pton error occured");
      return ERROR;
    } 
  */
  if( connect(sockfd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0)
    {
      perror("Error : Connect Failed");
      return ERROR;
    } 
  sh->fd = sockfd;
  sh->sent_bytes = 0;
  sh->received_bytes = 0;
  return OK;
}

result tcp_listen(int port, socket_handle* sh) {
  int listenfd = 0;
  struct sockaddr_in serv_addr; 

  if((listenfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      perror("Error : Could not create socket");
      return ERROR;
    } 
  memset(&serv_addr, '0', sizeof(serv_addr)); 
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_addr.s_addr = htonl(INADDR_ANY);
  serv_addr.sin_port = htons(port); 

  if (bind(listenfd, (struct sockaddr*)&serv_addr, sizeof(serv_addr)) < 0) {
    perror("bind");
    return ERROR;
  }
    
  if (listen(listenfd, 10) < 0) {
    perror("listen");
    return ERROR;
  }
  sh->fd = listenfd;
  return OK;
}

result tcp_accept(socket_handle* lh, socket_handle* conn) {
  int sockfd = 0;
  sockfd = accept(lh->fd, (struct sockaddr*)NULL, NULL); 
  if( sockfd < 0)
    {
      perror("Error : accept Failed");
      return ERROR;
    } 
  conn->fd = sockfd;
  return OK;
}


result tcp_write_all(socket_handle* conn, uint8_t* buf, uint64_t len) {
  if (write(conn->fd, buf, len) < len) {
    perror("write did not write all");
    return ERROR;
  }
  conn->sent_bytes += len;
  return OK;
}    


result tcp_read_all(socket_handle* conn, uint8_t* buf, int len) {
  int got = 0;
  while (got < len) {
    int n = read(conn->fd, buf+got, len-got);
    if (n == 0) {
      perror("early end of file");
      return ERROR;
    }
    if (n < 0) {
      perror("socket read error");
      return ERROR;
    }
    got += n;
  }
  conn->received_bytes += got;
  return OK;
}

result tcp_close(socket_handle* conn) {
  shutdown(conn->fd,2);
  printf("Sent %llu bytes, Received %llu bytes\n",conn->sent_bytes,conn->received_bytes);
  return OK;
}
