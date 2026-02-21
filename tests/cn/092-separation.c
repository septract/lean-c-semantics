// Test: Separation - writing to one pointer does not affect another
// Two owned pointers to different allocations; write to p, verify q unchanged

int write_and_read(int *p, int *q)
/*@ requires take vp = RW<int>(p);
             take vq = Owned<int>(q);
    ensures take wp = RW<int>(p);
            take wq = Owned<int>(q);
            wp == 42i32;
            wq == vq;
            return == vq; @*/
{
    *p = 42;
    return *q;
}

int main(void)
{
    int x = 1;
    int y = 99;
    return write_and_read(&x, &y);
}
