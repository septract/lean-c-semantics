// CN test: Write a known value to a memory cell and verify
// From cn-tutorial: write_1.c (adapted Owned for RW)
// Tests: write with postcondition value check

void write_cell(int *cell)
/*@ requires take CellPre = Owned<signed int>(cell);
    ensures
      take CellPost = Owned<signed int>(cell);
      CellPost == 7; @*/
{
  *cell = 7;
}

int main(void)
{
  int x = 0;
  write_cell(&x);
  return x;
}
