// CN test: Resource leak - should FAIL
// Not returning ownership that was taken
#include <stdlib.h>

void leak_resource(int *p)
/*@ requires take v = Owned<int>(p);
    ensures true; @*/  // ERROR: should return Owned<int>(p)
{
  *p = 42;
  // Resource consumed but not returned
}

int main(void)
{
  int x = 0;
  leak_resource(&x);
  return x;  // Can we still access x?
}
