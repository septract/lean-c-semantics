// Test: Return value mismatch (should fail)
// Ensures clause says return == x but we return x + 1

int wrong_return(int x)
/*@ requires x < 1000;
    ensures return == x; @*/
{
    return x + 1;  // Wrong! Should be x
}

int main(void)
{
    return wrong_return(5);
}
