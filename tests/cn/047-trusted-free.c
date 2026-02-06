// CN test: Trusted free function consuming a resource
// From cn-tutorial: free_1.c
// Tests: trusted keyword, function calls with specs, resource consumption
// NEEDS: RW resource type, function call verification (callee spec lookup)

void my_free_int(int *target)
/*@ trusted;
    requires take ToFree = RW<int>(target); @*/
{}

void free_one(int *x, int *y)
/*@ requires
      take Xpre = RW<int>(x);
      take Ypre = RW<int>(y);
    ensures take Ypost = RW<int>(y); @*/
{
  *x = 7;
  my_free_int(x);
}

int main(void)
{
  int a = 1, b = 2;
  free_one(&a, &b);
  return b;
}
