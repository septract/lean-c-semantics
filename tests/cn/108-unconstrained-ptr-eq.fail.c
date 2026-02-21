// Ported from CN test suite: unconstrained_ptr_eq.error.c
int f(int *p, int *q)
/*@
ensures
    return == 0i32;
@*/
{
    return p == q;
}

