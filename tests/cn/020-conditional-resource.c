// Test: Conditional with resource access
// Both branches access the same resource - should pass

int conditional_read(int *p, int flag)
/*@ requires take v = Owned<int>(p);
    ensures take v2 = Owned<int>(p);
            v == v2; @*/
{
    if (flag) {
        return *p;
    } else {
        return *p + 1;
    }
}
