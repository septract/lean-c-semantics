// struct-004-union-type-pun.c
// Write one union member, read another (type punning).
// Exercises: PEunion construction and PEmemberof on union types.
// Note: reading a different member than was last written may be
// implementation-defined; we want Cerberus to exercise union code paths.

union Pun {
    int i;
    unsigned int u;
};

int main(void) {
    union Pun p;
    p.i = -1;

    // Reading the unsigned member after writing the signed member.
    // On two's complement (universal), -1 as unsigned int is UINT_MAX.
    unsigned int val = p.u;

    // Just check that the value is non-zero.
    if (val != 0)
        return 1;
    return 0;
}
