#include <stdio.h>
#include "bedrock.h"

int bedrock_stack_size = 10 * 1024;

BEDROCK_THREAD(shouter) {
  puts("Hello, world!");
  bedrock_yield();
  puts("Encore!");
  bedrock_yield();
  puts("YEAH!");
  bedrock_exit();
}
BEDROCK_WRAP(shouter)

BEDROCK_THREAD(accepter) {
  char buf[1024];

  puts("Listening....");
  fd_t listener = bedrock_listen(6666);
  puts("Started listening.");
  fd_t remote = bedrock_accept(listener);
  puts("Got one!");
  bedrock_write(remote, "How's it going?\n", 16);
  unsigned size = bedrock_read(remote, buf, sizeof buf - 1);
  if (size == 0) {
    puts("Uh oh!");
    bedrock_exit();
  }
  buf[size] = 0;
  printf("Server received: %s", buf);
  bedrock_write(remote, buf, size);
  bedrock_close(remote);
  bedrock_close(listener);
  bedrock_exit();
}
BEDROCK_WRAP(accepter)

BEDROCK_THREAD(connecter) {
  char buf[1024];

  puts("Connecting....");
  fd_t server = bedrock_connect("localhost:80", 14);
  bedrock_write(server, "GET / HTTP/1.0\r\n\r\n", 18);
  unsigned size = bedrock_read(server, buf, sizeof buf - 1);
  if (size == 0) {
    puts("Uh oh!");
    bedrock_exit();
  }
  buf[size] = 0;
  printf("Client received: %s", buf);
  bedrock_close(server);
  bedrock_exit();
}
BEDROCK_WRAP(connecter)

void rtos_main() {
  bedrock_spawn(shouter);
  bedrock_spawn(accepter);
  bedrock_spawn(connecter);
}
