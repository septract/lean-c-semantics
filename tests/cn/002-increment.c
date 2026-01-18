// CN test: Increment pointer value
void inc(int *p)
/*@ requires take v = Owned<int>(p);
             v >= 0;
    ensures take v2 = Owned<int>(p);
            v2 == v + 1; @*/
{
  *p = *p + 1;
}

int main(void)
{
  int x = 0;
  inc(&x);
  return x;
}
