// From cn-tutorial: resource taken in pre but not returned in post
void ownership_neg_1(int *p)
/*@ requires take P = RW(p); @*/
/*@ ensures true; @*/
{
  ;
}
