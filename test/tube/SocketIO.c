#include "IO.h"

SocketIO_socket init_socket;

SocketIO_sresult SocketIO_tcp_connect(char* host, int port, SocketIO_socket* sh) {
  int sockfd = 0, n = 0;
  struct sockaddr_in serv_addr; 
  if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      perror("Error : Could not create socket");
      return SocketError;
    } 

  struct hostent *server = gethostbyname(host);
  if (server == NULL) {
    perror("SocketError, DNS lookup on host failed");
    return SocketError;
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
      return SocketError;
    } 
  sh->fd = sockfd;
  sh->sent_bytes = 0;
  sh->received_bytes = 0;
  return SocketOk;
}

SocketIO_sresult SocketIO_tcp_listen(int port, SocketIO_socket* sh) {
  int listenfd = 0;
  struct sockaddr_in serv_addr; 

  if((listenfd = socket(AF_INET, SOCK_STREAM, 0)) < 0)
    {
      perror("Error : Could not create socket");
      return SocketError;
    } 
  memset(&serv_addr, '0', sizeof(serv_addr)); 
  serv_addr.sin_family = AF_INET;
  serv_addr.sin_addr.s_addr = htonl(INADDR_ANY);
  serv_addr.sin_port = htons(port); 

  if (bind(listenfd, (struct sockaddr*)&serv_addr, sizeof(serv_addr)) < 0) {
    perror("bind");
    return SocketError;
  }
    
  if (listen(listenfd, 10) < 0) {
    perror("listen");
    return SocketError;
  }
  sh->fd = listenfd;
  return SocketOk;
}

SocketIO_sresult SocketIO_tcp_accept(SocketIO_socket* lh, SocketIO_socket* conn) {
  int sockfd = 0;
  sockfd = accept(lh->fd, (struct sockaddr*)NULL, NULL); 
  if( sockfd < 0)
    {
      perror("Error : accept Failed");
      return SocketError;
    } 
  conn->fd = sockfd;
  return SocketOk;
}


SocketIO_sresult SocketIO_tcp_write_all(SocketIO_socket* conn, uint8_t* buf, uint64_t len) {
  if (write(conn->fd, buf, len) < len) {
    perror("write did not write all");
    return SocketError;
  }
  conn->sent_bytes += len;
  return SocketOk;
}    


SocketIO_sresult SocketIO_tcp_read_all(SocketIO_socket* conn, uint8_t* buf, int len) {
  int got = 0;
  while (got < len) {
    int n = read(conn->fd, buf+got, len-got);
    if (n == 0) {
      perror("early end of file");
      return SocketError;
    }
    if (n < 0) {
      perror("socket read error");
      return SocketError;
    }
    got += n;
  }
  conn->received_bytes += got;
  return SocketOk;
}

SocketIO_sresult SocketIO_tcp_close(SocketIO_socket* conn) {
  shutdown(conn->fd,2);
  printf("Sent %llu bytes, Received %llu bytes\n",conn->sent_bytes,conn->received_bytes);
  return SocketOk;
}

