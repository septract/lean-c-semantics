// mem3-008-eff-member-shift.c
// Exercise eff_member_shift_ptrval in impl_mem.ml (L2359)
// Access struct member through pointer (effectful path)
struct S { int x; int y; int z; };
void set_members(struct S *p) {
    p->x = 10;  // eff_member_shift_ptrval for each member access
    p->y = 20;
    p->z = 30;
}
int main(void) {
    struct S s;
    set_members(&s);
    if (s.x != 10) return 1;
    if (s.y != 20) return 2;
    if (s.z != 30) return 3;
    return 0;
}
