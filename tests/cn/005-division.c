// CN test: Division with precondition
int division(int x, int y)
/*@ requires y != 0;
    ensures return == x / y; @*/
{
  return x / y;
}

int main(void)
{
  return division(10, 2);
}
