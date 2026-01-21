// Test: Local variable allocation and use
// Tests create/store/load sequence for locals

int local_var_test(void)
/*@ ensures return == 42; @*/
{
    int x = 42;
    return x;
}
