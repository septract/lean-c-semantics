// Test: return equals literal in spec
// Isolates: spec-side integer literal typing
int always42(int x)
/*@ ensures return == 42; @*/
{
    return 42;
}

int main(void)
{
    return always42(0);
}
