#include <stdio.h>

#include "list.h"

list server(unsigned input[], unsigned inputSize, unsigned data[], unsigned dataSize);
extern unsigned *data, *cmd, dataSize, cmdSize;

int main() {
  list output = server(cmd, cmdSize, data, dataSize);

  for (; output; output = output->next)
    printf("%u\n", output->data);

  return 0;
}
