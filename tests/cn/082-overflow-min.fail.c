// From cn-tutorial: decrement at MIN_INT causes overflow
void overflow_neg_2(int i)
/*@ requires i == MINi32(); @*/
{
  i = i - 1;
}
