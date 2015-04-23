#include <stdlib.h>
#include <stdio.h>

#define HEAP_SIZE (100*1024*1024)
#define STACK_SIZE 1000
#define MAX_LEN ((HEAP_SIZE-1) / 2 - 2)

unsigned bedrock_heap[HEAP_SIZE+STACK_SIZE];

unsigned bedrock_main();

int main(int argc, char *argv[]) {
  if (argc < 2) {
    puts("Please run me with the desired list size as a command-line argument.");
    return 1;
  }

  unsigned size = atoi(argv[1]);

  if (size >= MAX_LEN) {
    printf("Length must be < %u.\n", MAX_LEN);
    return 1;
  }

  bedrock_heap[0] = 4 * (2*size + 3);
  bedrock_heap[1] = (size == 0 ? 0 : 3*4);
  bedrock_heap[2*size + 3] = HEAP_SIZE - 5 - 2*size;
  bedrock_heap[2*size + 4] = 0;
  unsigned sum = 0, i;

  for (i = 0; i < size; ++i) {
    int n = rand();
    sum += n;
    bedrock_heap[2*i + 3] = n;
    bedrock_heap[2*i + 4] = (i == size-1 ? 0 : 4 * (2 * i + 5));
  }

  printf("EXPECTING: %u\n", sum);
  printf("   ANSWER: %u\n", bedrock_main());
  return 0;
}

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program terminated.");
  exit(0);
}
