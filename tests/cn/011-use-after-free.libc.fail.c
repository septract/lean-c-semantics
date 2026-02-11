// CN test: Use after free - should FAIL
// Reading memory after it's been freed is undefined behavior
#include <stdlib.h>

int use_after_free(int *p)
/*@ requires take v = Owned<int>(p);
    ensures true; @*/
{
  free(p);
  return *p;  // ERROR: p already freed
}

int main(void)
{
  int *p = malloc(sizeof(int));
  if (p) {
    *p = 42;
    use_after_free(p);
  }
  return 0;
}
