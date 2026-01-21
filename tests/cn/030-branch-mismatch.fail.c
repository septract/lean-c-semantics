// Test: Branch resource mismatch - should fail
// One branch frees the resource, other keeps it

void branch_mismatch(int *p, int flag)
/*@ requires take v = Owned<int>(p);
    ensures true; @*/
{
    if (flag) {
        // This branch keeps the resource
        *p = 1;
    }
    // Other branch does nothing - different final resources!
}
