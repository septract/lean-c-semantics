// Test: Pointer equality comparison
// When two pointers are known equal, they alias the same resource

int check_ptr_eq(int *p, int *q)
/*@ requires take vp = Owned<int>(p);
             ptr_eq(p, q);
    ensures take wp = Owned<int>(q);
            return == vp; @*/
{
    if (p == q) {
        return *p;
    }
    return 0;
}

int main(void)
{
    int x = 7;
    return check_ptr_eq(&x, &x);
}
