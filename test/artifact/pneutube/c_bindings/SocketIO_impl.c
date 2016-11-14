#ifndef SOCKET_IO_IMPL
#define SOCKET_IO_IMPL

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

FileIO_Types_socket init_socket;

FileIO_Types_sresult SocketIO_tcp_connect(char* host, int port, FileIO_Types_socket* sh) {
  int sockfd = 0, n = 0;
  struct sockaddr_in serv_addr; 
  if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      perror("Error : Could not create socket");
      return FileIO_Types_sresult_SocketError;
    }

  struct hostent *server = gethostbyname(host);
  if (server == NULL) {
    perror("SocketError, DNS lookup on host failed");
    return FileIO_Types_sresult_SocketError;
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
      return SocketError;
    } 
  */
  if( connect(sockfd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0)
    {
      perror("Error : Connect Failed");
      return FileIO_Types_sresult_SocketError;
    } 
  sh->socket_fd = sockfd;
  sh->sent_bytes = 0;
  sh->received_bytes = 0;
  return FileIO_Types_sresult_SocketOk;
}

FileIO_Types_sresult SocketIO_tcp_listen(int port, FileIO_Types_socket* sh) {
  int listenfd = 0;
  struct sockaddr_in serv_addr; 

  if((listenfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      perror("Error : Could not create socket");
      return FileIO_Types_sresult_SocketError;
    } 
  memset(&serv_addr, '0', sizeof(serv_addr)); 
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_addr.s_addr = htonl(INADDR_ANY);
  serv_addr.sin_port = htons(port); 

  if (bind(listenfd, (struct sockaddr*)&serv_addr, sizeof(serv_addr)) < 0) {
    perror("bind");
    return FileIO_Types_sresult_SocketError;
  }
    
  if (listen(listenfd, 10) < 0) {
    perror("listen");
    return FileIO_Types_sresult_SocketError;
  }
  sh->socket_fd = listenfd;
  return FileIO_Types_sresult_SocketOk;
}

FileIO_Types_sresult SocketIO_tcp_accept(FileIO_Types_socket* lh, FileIO_Types_socket* conn) {
  int sockfd = 0;
  sockfd = accept(lh->socket_fd, (struct sockaddr*)NULL, NULL); 
  if( sockfd < 0)
    {
      perror("Error : accept Failed");
      return FileIO_Types_sresult_SocketError;
    } 
  conn->socket_fd = sockfd;
  return FileIO_Types_sresult_SocketOk;
}


FileIO_Types_sresult SocketIO_tcp_write_all(FileIO_Types_socket* conn, uint8_t* buf, uint64_t len) {
  if (write(conn->socket_fd, buf, len) < len) {
    perror("write did not write all");
    return FileIO_Types_sresult_SocketError;
  }
  conn->sent_bytes += len;
  return FileIO_Types_sresult_SocketOk;
}    


FileIO_Types_sresult SocketIO_tcp_read_all(FileIO_Types_socket* conn, uint8_t* buf, int len) {
  int got = 0;
  while (got < len) {
    int n = read(conn->socket_fd, buf+got, len-got);
    if (n == 0) {
      perror("early end of file");
      return FileIO_Types_sresult_SocketError;
    }
    if (n < 0) {
      perror("socket read error");
      return FileIO_Types_sresult_SocketError;
    }
    got += n;
  }
  conn->received_bytes += got;
  return FileIO_Types_sresult_SocketOk;
}

FileIO_Types_sresult SocketIO_tcp_close(FileIO_Types_socket* conn) {
  shutdown(conn->socket_fd,2);
  printf("Sent %lu bytes, Received %lu bytes\n",conn->sent_bytes,conn->received_bytes);
  return FileIO_Types_sresult_SocketOk;
}

#endif
