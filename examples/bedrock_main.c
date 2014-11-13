#include <stdlib.h>
#include <stdio.h>

#define HEAP_SIZE (100*1024*1024)
#define STACK_SIZE 1000

unsigned bedrock_heap[HEAP_SIZE+STACK_SIZE];

unsigned bedrock_main();

int main(int argc, char *argv[]) {
  bedrock_heap[0] = 3;
  bedrock_heap[1] = 0;
  bedrock_heap[2] = 0;
  bedrock_heap[3] = HEAP_SIZE-5;
  bedrock_heap[4] = 0;
  printf("ANSWER: %u\n", bedrock_main());
  return 0;
}

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program terminated.");
  exit(0);
}
