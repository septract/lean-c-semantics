// CN test: Pointer aliasing - two variables point to same location
// From cn-tutorial: write_3.c
// Tests: pointer equality constraint in spec, aliased access
// NEEDS: RW resource type, aliasing reasoning (cell1 == cell2)

void write_aliased(int *cell1, int *cell2)
/*@ requires
      take Cell1Pre = RW<int>(cell1);
      cell1 == cell2;
    ensures
      take Cell2Post = RW<int>(cell2);
      Cell2Post == 8i32; @*/
{
  *cell1 = 7;
  *cell2 = 8;
}

int main(void)
{
  int x = 0;
  write_aliased(&x, &x);
  return x;
}
