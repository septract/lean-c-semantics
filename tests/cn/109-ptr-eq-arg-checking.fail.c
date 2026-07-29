// Ported from CN test suite: ptr_eq_arg_checking.error.c
void f(unsigned int *x, unsigned int y)
/*@ requires ptr_eq(x,y);
   ensures true; @*/
{ }
