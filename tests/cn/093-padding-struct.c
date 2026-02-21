// Test: Struct with padding between members
// struct { char a; int b; } has padding after 'a' for alignment

struct padded {
    char a;
    int b;
};

int get_b(struct padded *p)
/*@ requires take v = Owned<struct padded>(p);
    ensures take v2 = Owned<struct padded>(p);
            return == v.b;
            v == v2; @*/
{
    return p->b;
}

int main(void)
{
    struct padded s;
    s.a = 'x';
    s.b = 42;
    return get_b(&s);
}
