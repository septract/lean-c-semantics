// Test: Return value from pointer dereference
// Tests return value when loading from owned pointer

int get_value(int *p)
/*@ requires take v = Owned<signed int>(p);
    ensures take v2 = Owned<signed int>(p);
            v == v2;
            return == v; @*/
{
    return *p;
}

int main(void)
{
    int x = 42;
    return get_value(&x);
}
