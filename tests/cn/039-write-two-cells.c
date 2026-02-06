// CN test: Write known values to two memory cells
// From cn-tutorial: write_2.c (adapted Owned for RW)
// Tests: two independent writes with postcondition value checks

void write_two(int *cell1, int *cell2)
/*@ requires take Cell1Pre = Owned<signed int>(cell1);
             take Cell2Pre = Owned<signed int>(cell2);
    ensures take Cell1Post = Owned<signed int>(cell1);
            take Cell2Post = Owned<signed int>(cell2);
            Cell1Post == 7; Cell2Post == 8; @*/
{
  *cell1 = 7;
  *cell2 = 8;
}

int main(void)
{
  int a = 0, b = 0;
  write_two(&a, &b);
  return a + b;
}
