// Test: Postcondition constraint violation
// Should fail - return value doesn't match ensures clause
// NOTE: Cannot detect with trivial oracle - needs real SMT solver

int bad_return(int x)
/*@ requires 0 < x;
    ensures return == x + 1; @*/
{
    return x;  // Wrong! Should be x + 1
}
