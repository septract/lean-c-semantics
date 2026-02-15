// union3-002-type-pun-int-float.c
// Exercise union type punning: write one member, read another
// This is implementation-defined but exercises MVunion abst paths
union U { int i; float f; };
int main(void) {
    union U u;
    u.i = 0x40490FDB; // bit pattern of ~3.14159f (IEEE 754)
    // Just access the float member to exercise the path; don't check the value
    float f = u.f;
    (void)f;
    return 0;
}
