// From cn-tutorial: postcondition claims resource that was never taken
void ownership_neg_2(int *p)
/*@ requires true; @*/
/*@ ensures take P_ = RW(p); @*/
{
  ;
}
