// CN test: Increment pointer value
void inc(int *p)
/*@ requires take v = Owned<int>(p);
             v >= 0i32; v <= 2147483646i32;
    ensures take v2 = Owned<int>(p);
            v2 == v + 1i32; @*/
{
  *p = *p + 1;
}

int main(void)
{
  int x = 0;
  inc(&x);
  return x;
}
