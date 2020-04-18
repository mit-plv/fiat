#include <limits.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>
#include <signal.h>
#include <fcntl.h>

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program terminated.");
  exit(0);
}

void _sys_printInt(unsigned n) {
  printf("Bedrock> %u\n", n);
}

static void ignoreSigpipe() {
  signal(SIGPIPE, SIG_IGN);
}

unsigned _sys_listen(unsigned port) {
#ifdef DEBUG
  fprintf(stderr, "listen(%u)\n", port);
#endif

  ignoreSigpipe();

  int sock = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in sa;

  if (sock == -1) {
    perror("socket");
    exit(1);
  }

  int one = 1;

  if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one))) {
    perror("setsockopt");
    exit(1);
  }

  if (ioctl(sock, FIONBIO, &one)) {
    perror("ioctl");
    exit(1);
  }

  memset(&sa, 0, sizeof(sa));
  sa.sin_family = AF_INET;
  sa.sin_port = htons(port);
  sa.sin_addr.s_addr = INADDR_ANY;

  if (bind(sock, (struct sockaddr *)&sa, sizeof(sa))) {
    perror("bind");
    exit(1);
  }

  if (listen(sock, 10)) {
    perror("listen");
    exit(1);
  }

#ifdef DEBUG
  fprintf(stderr, "listen(%u) = %u\n", port, sock);
#endif

  return sock;
}

unsigned _sys_accept(unsigned sock) {
#ifdef DEBUG
  fprintf(stderr, "accept(%u)\n", sock);
#endif

  int new_sock = accept(sock, NULL, NULL), one = 1;

  if (new_sock == -1) {
    perror("accept");
    exit(1);
  }

  if (ioctl(new_sock, FIONBIO, &one)) {
    perror("ioctl");
    exit(1);
  }

#ifdef DEBUG
  fprintf(stderr, "accept(%u) = %u\n", sock, new_sock);
#endif

  return new_sock;
}

static int fake_fd = -1;

static unsigned fake_connect() {
  if (fake_fd == -1) {
    fake_fd = open("/dev/null", O_RDWR);

    if (fake_fd < 0) {
      perror("open");
      exit(1);
    }
  }

  return fake_fd;
}

unsigned _sys_connect(char *address, unsigned size) {
  ignoreSigpipe();

  int i;
  char *addr = malloc(size+1), *host, *port;
  struct addrinfo hints, *res;
  int sockfd;
  memcpy(addr, address, size);

  if (size == 0) {
    fprintf(stderr, "Empty connect() string\n");
    free(addr);
    return fake_connect();
  }

  // Find last printing character, which we'll treat as the end of the port string.
  i = size-1;
  while (1) {
    if (isprint(addr[i]) && addr[i] != '/') {
      addr[i+1] = 0;
      break;
    }

    if (i <= 0) {
      fprintf(stderr, "Bad connect() string [1]\n");
      free(addr);
      return fake_connect();
    }

    --i;
  }

  // Find a ':' beforehand, to mark the beginning of the port.
  while (1) {
    if (addr[i] == ':') {
      addr[i] = 0;
      port = addr + (i+1);
      --i;
      break;
    }

    if (i <= 0) {
      fprintf(stderr, "Bad connect() string [2]\n");
      free(addr);
      return fake_connect();
    }

    --i;
  }

  if (i < 0) {
    fprintf(stderr, "Bad connect() string [3]\n");
    free(addr);
    return fake_connect();
  }

  // Find the beginning of the host part of the string.
  while (1) {
    if (!isalnum(addr[i]) && addr[i] != '.' && addr[i] != '-' && addr[i] != '_') {
      host = addr + (i+1);
      break;
    }

    if (i <= 0) {
      host = addr;
      break;
    }

    --i;
  }

  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;

  i = getaddrinfo(host, port, &hints, &res);
  if (i) {
    fprintf(stderr, "getaddrinfo(%s:%s): %s\n", host, port, gai_strerror(i));
    free(addr);
    return fake_connect();
  }

  sockfd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);

  if (sockfd == -1) {
    perror("socket");
    free(addr);
    return fake_connect();
  }

  i = connect(sockfd, res->ai_addr, res->ai_addrlen);

  if (i && errno != EINPROGRESS) {
    perror("connect");
    close(sockfd);
    free(addr);
    return fake_connect();
  }

  free(addr);
  return sockfd;
}

unsigned _sys_read(unsigned sock, void *buf, unsigned count) {
  if (fake_fd != -1 && sock == fake_fd)
    return 0;

  ssize_t n = read(sock, buf, count);

  if (n == -1) {
    if (errno == ECONNRESET)
      n = 0;
    else {
      perror("read");
      exit(1);
    }
  }

#ifdef DEBUG
  fprintf(stderr, "read(%u, %p, %u) = %u\n", sock, buf, count, n);
#endif

  return n;
}

unsigned _sys_write(unsigned sock, void *buf, unsigned count) {
  if (fake_fd != -1 && sock == fake_fd)
    return count;

  ssize_t n = write(sock, buf, count);

  if (n == -1) {
    if (errno == EPIPE)
      n = count;
      // To make verification simpler, let's pretend writes to a closed socket all succeed in full.
    else {
      perror("write");
      exit(1);
    }
  }

#ifdef DEBUG
  fprintf(stderr, "write(%u, %p, %u) = %u\n", sock, buf, count, n);
#endif

  return n;
}

static unsigned epoll, num_fds, num_outstanding;
static uint32_t *fds;

static void init_epoll() {
  if (epoll == 0) {
    epoll = epoll_create(1);

    if (epoll == -1) {
      perror("epoll_create");
      exit(1);
    }

    fds = malloc(0);
  }
}

static int fake_reads, fake_writes;

unsigned _sys_declare(unsigned sock, unsigned mode) {
  if (fake_fd != -1 && sock == fake_fd) {
    if (mode)
      ++fake_writes;
    else
      ++fake_reads;

    return 2 * fake_fd + (mode ? 1 : 0);
  }

  init_epoll();

  if (sock >= num_fds) {
    fds = realloc(fds, sizeof(uint32_t) * (sock+1));
    memset(fds + num_fds, 0, sizeof(uint32_t) * (sock+1 - num_fds));
    num_fds = sock;
  }

  uint32_t mask = mode ? EPOLLOUT : EPOLLIN;

  if (fds[sock] & mask)
    return UINT_MAX;

  int is_new = 0;

  if (fds[sock] == 0) {
    ++num_outstanding;
    is_new = 1;
  }

  fds[sock] |= mask;

  struct epoll_event event;

  event.events = fds[sock];
  event.data.fd = sock;

  if (epoll_ctl(epoll, is_new ? EPOLL_CTL_ADD : EPOLL_CTL_MOD, sock, &event)) {
    perror("epoll_ctl");
    exit(1);
  }

  unsigned index = 2 * sock + (mode ? 1 : 0);

#ifdef DEBUG
  fprintf(stderr, "declare(%u, %u) = %u\n", sock, mode, index);
#endif

  return index;
}

unsigned _sys_wait(unsigned blocking) {
  if (fake_reads > 0) {
    --fake_reads;
    return 2 * fake_fd;
  } else if (fake_writes > 0) {
    --fake_writes;
    return 2 * fake_fd + 1;
  }

  if (num_outstanding == 0)
    return UINT_MAX;

  init_epoll();

  struct epoll_event event;
  int count = epoll_wait(epoll, &event, 1, blocking ? -1 : 0);

  if (count == -1) {
    perror("epoll_wait");
    exit(1);
  }

  if (count == 0)
    return UINT_MAX;

  int fd = event.data.fd;
  uint32_t mask = (event.events & EPOLLIN) ? EPOLLIN : EPOLLOUT;

  fds[fd] &= ~mask;

  if (fds[fd] == 0)
    --num_outstanding;

  event.events = fds[fd];

  if (epoll_ctl(epoll, (fds[fd] == 0) ? EPOLL_CTL_DEL : EPOLL_CTL_MOD, fd, &event)) {
    perror("epoll_ctl");
    exit(1);
  }

  unsigned index = 2 * fd + ((mask == EPOLLIN) ? 0 : 1);

#ifdef DEBUG
  fprintf(stderr, "wait(%u) = %u\n", blocking, index);
#endif

  return index;
}

void _sys_close(unsigned fd) {
  if (fake_fd != -1 && fd == fake_fd)
    return;

  if (fd < num_fds && fds[fd]) {
    fds[fd] = 0;
    --num_outstanding;
  }

  if (close(fd) == -1) {
    perror("close");
    exit(1);
  }
}
