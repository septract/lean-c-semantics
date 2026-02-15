// mem3-002-bool-trap.c
// Exercise _Bool trap representation check in impl_mem.ml
// Writing a non-0/1 value to a _Bool via char pointer creates a trap representation
int main(void) {
    _Bool b = 0;
    unsigned char *p = (unsigned char*)&b;
    *p = 2; // write non-0/1 value to _Bool storage
    // Reading b would be a trap representation (UB)
    // Just the write exercises the store path
    return 0;
}
