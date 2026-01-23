// Test: Write to uninitialized memory (should fail)
// Local variable has Uninit, but we try to read before writing

int write_then_read(void)
/*@ ensures true; @*/
{
    int x;
    int y = x;  // Reading uninitialized x
    x = 42;     // Now we write
    return y;
}
