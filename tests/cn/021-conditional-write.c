// Test: Conditional write to memory
// Both branches write to the same resource

void conditional_write(int *p, int flag, int val1, int val2)
/*@ requires take v = Owned<int>(p);
    ensures take v2 = Owned<int>(p); @*/
{
    if (flag) {
        *p = val1;
    } else {
        *p = val2;
    }
}
