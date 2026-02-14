// From cn-tutorial: increment at MAX_INT causes overflow
void overflow_neg_1(int i)
/*@ requires i == MAXi32(); @*/
{
  i = i + 1;
}
