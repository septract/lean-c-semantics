// CN test: Double free - should FAIL
// Freeing the same memory twice is undefined behavior
#include <stdlib.h>

void double_free(int *p)
/*@ requires take v = Owned<int>(p);
    ensures true; @*/
{
  free(p);
  free(p);  // ERROR: p already freed
}

int main(void)
{
  int *p = malloc(sizeof(int));
  if (p) double_free(p);
  return 0;
}
