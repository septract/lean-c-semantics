// CN test: Swap two values
void swap(int *a, int *b)
/*@ requires take va = Owned<int>(a);
             take vb = Owned<int>(b);
    ensures take va2 = Owned<int>(a);
            take vb2 = Owned<int>(b);
            va2 == vb;
            vb2 == va; @*/
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

int main(void)
{
  int x = 1;
  int y = 2;
  swap(&x, &y);
  return x + y;
}
