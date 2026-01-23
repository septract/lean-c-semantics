// Simple CN test: Owned pointer with read
int read(int *p)
/*@ requires take v = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
            v == v2;
            return == v; @*/
{
  return *p;
}

int main(void)
{
  int x = 42;
  return read(&x);
}
