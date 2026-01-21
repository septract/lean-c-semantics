// Test: Struct field access via pointer dereference
// Tests memberShift handling

struct point {
    int x;
    int y;
};

int get_x(struct point *p)
/*@ requires take v = Owned<struct point>(p);
    ensures take v2 = Owned<struct point>(p);
            return == v.x; @*/
{
    return p->x;
}
