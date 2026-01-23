// CN test: Read uninitialized - should FAIL
// Reading from uninitialized memory is undefined behavior
#include <stdlib.h>

int read_uninit(void)
/*@ ensures true; @*/
{
  int x;      // uninitialized
  return x;   // ERROR: reading uninitialized value
}

int main(void)
{
  return read_uninit();
}
