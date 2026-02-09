struct inner { int val; };
struct outer { struct inner s; int extra; };

int get_inner(struct outer *p)
/*@ requires take o = Owned<struct outer>(p);
    ensures take o2 = Owned<struct outer>(p);
            return == o.s.val;
            o == o2; @*/
{
    return p->s.val;
}
