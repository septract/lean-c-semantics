// Test: Two pointers to different locations
// Tests handling multiple resources

int sum_two(int *p, int *q)
/*@ requires take vp = Owned<signed int>(p);
             take vq = Owned<signed int>(q);
    ensures take vp2 = Owned<signed int>(p);
            take vq2 = Owned<signed int>(q);
            return == vp + vq; @*/
{
    return *p + *q;
}
