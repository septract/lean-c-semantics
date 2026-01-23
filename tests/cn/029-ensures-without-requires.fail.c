// Test: Ensures resource without requiring it first
// Should fail - can't produce a resource from nothing

int bad_ensures(int *p)
/*@ ensures take v = Owned<int>(p); @*/
{
    return 0;
}
