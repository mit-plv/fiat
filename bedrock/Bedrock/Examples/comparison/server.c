#include <stdlib.h>
#include <assert.h>

#define MAX(x, y) ((x) < (y) ? (y) : (x))

#include "list.h"

list server(unsigned input[], unsigned inputSize, unsigned data[], unsigned dataSize) {
  unsigned pos;
  list output = NULL;

  for (pos = 0; pos < inputSize; ) {
    switch (input[pos]) {
    case 0: {
      unsigned index = input[pos+1], valueLowerBound = input[pos+2];
      list cell = malloc(sizeof(struct list));
      pos += 3;

      assert(index < dataSize);

      cell->data = !!(data[index] >= valueLowerBound);
      cell->next = output;
      output = cell;
      break;
    }
    case 1: {
      unsigned lowerBound = input[pos+1], upperBound = input[pos+2], i, acc = 0;
      list cell = malloc(sizeof(struct list));
      pos += 3;

      for (i = 0; i < dataSize; ++i)
        if (lowerBound <= data[i] && data[i] <= upperBound)
          acc = MAX(acc, data[i]);

      cell->data = acc;
      cell->next = output;
      output = cell;
      break;
    }
    case 2: {
      unsigned indexLowerBound = input[pos+1], valueUpperBound = input[pos+2], i;
      pos += 3;

      for (i = indexLowerBound; i < dataSize; ++i) {
        if (data[i] <= valueUpperBound) {
          list cell = malloc(sizeof(struct list));
          cell->data = data[i];
          cell->next = output;
          output = cell;
        }
      }

      break;
    }
    default:
      assert(0);
    }
  }

  return output;
}
