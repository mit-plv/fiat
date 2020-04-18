/* Based on the following from Beej's socket tutorial:
** client.c -- a stream socket client demo
*/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <netdb.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <sys/socket.h>

#include <arpa/inet.h>

// get sockaddr, IPv4 or IPv6:
void *get_in_addr(struct sockaddr *sa)
{
  if (sa->sa_family == AF_INET) {
    return &(((struct sockaddr_in*)sa)->sin_addr);
  }

  return &(((struct sockaddr_in6*)sa)->sin6_addr);
}

int main(int argc, char *argv[])
{
  int sockfd, numbytes;  
  char *inbuf, *outbuf, *hostname, *port;
  struct addrinfo hints, *servinfo, *p;
  int rv, numThreads, numRequests, i, j, dataLength, status, combined = 0;
  char s[INET6_ADDRSTRLEN];

  if (argc != 6) {
    fprintf(stderr,"usage: %s <hostname> <port> <numThreads> <numRequests> <dataLength>\n", argv[0]);
    return 1;
  }

  hostname = argv[1];
  port = argv[2];
  numThreads = atoi(argv[3]);
  numRequests = atoi(argv[4]);
  dataLength = atoi(argv[5]);

  inbuf = malloc(dataLength);
  outbuf = malloc(dataLength);

  for (i = 0; i < numThreads; ++i) {
    if (!fork()) {
      memset(&hints, 0, sizeof hints);
      hints.ai_family = AF_UNSPEC;
      hints.ai_socktype = SOCK_STREAM;

      if ((rv = getaddrinfo(hostname, port, &hints, &servinfo)) != 0) {
        fprintf(stderr, "getaddrinfo: %s\n", gai_strerror(rv));
        return 1;
      }

      // loop through all the results and connect to the first we can
      for(p = servinfo; p != NULL; p = p->ai_next) {
        if ((sockfd = socket(p->ai_family, p->ai_socktype,
                             p->ai_protocol)) == -1) {
          perror("client: socket");
          continue;
        }

        if (connect(sockfd, p->ai_addr, p->ai_addrlen) == -1) {
          close(sockfd);
          perror("client: connect");
          continue;
        }

        break;
      }

      if (p == NULL) {
        fprintf(stderr, "client: failed to connect\n");
        return 2;
      }

      inet_ntop(p->ai_family, get_in_addr((struct sockaddr *)p->ai_addr),
                s, sizeof s);

      freeaddrinfo(servinfo); // all done with this structure

      srand(getpid() * time(NULL));

      for (j = 0; j < numRequests; ++j) {
        for (i = 0; i < dataLength; ++i)
          outbuf[i] = rand();

        // Initialize random data

        for (i = 0; i < dataLength; ) {
          numbytes = write(sockfd, outbuf + i, dataLength - i);

          if (numbytes <= 0) {
            perror("write");
            return 1;
          }

          i += numbytes;
        }

        for (i = 0; i < dataLength; ) {
          numbytes = read(sockfd, inbuf + i, dataLength - i);

          if (numbytes <= 0) {
            perror("read");
            return 1;
          }

          i += numbytes;
        }

        if (memcmp(inbuf, outbuf, dataLength)) {
          fprintf(stderr, "Wrong data echoed back!\n");

          for (i = 0; i < dataLength; ++i) {
            if (inbuf[i] != outbuf[i]) {
              fprintf(stderr, "First mismatch: %d -> %d, %d\n", i, inbuf[i], outbuf[i]);
              break;
            }
          }

          return 1;
        }
      }

      close(sockfd);

      return 0;
    }
  }

  for (i = 0; i < numThreads; ++i) {
    wait(&status);
    combined = combined || status;
  }

  if (combined)
    fprintf(stderr, "At least one child failed!\n");

  return combined;
}
