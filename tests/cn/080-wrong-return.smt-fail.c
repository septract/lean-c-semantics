// From cn-tutorial: postcondition claims non-zero but returns zero
int arith_neg_1()
/*@ ensures return != 0i32; @*/
{
  return 0;
}
