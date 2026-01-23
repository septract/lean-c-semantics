// CN test: Missing resource - should FAIL
// Accessing memory without ownership

int missing_resource(int *p)
/*@ ensures true; @*/  // ERROR: no Owned<int>(p) in precondition, but body accesses *p
{
  return *p;
}

int main(void)
{
  int x = 42;
  return missing_resource(&x);
}
