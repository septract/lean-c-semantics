// mem3-001-bool-load.c
// Exercise _Bool load path and is_Bool/is_trap check in impl_mem.ml (L1580-1598)
int main(void) {
    _Bool b1 = 1;
    if (b1 != 1) return 1;
    _Bool b2 = 0;
    if (b2 != 0) return 2;
    // Store and load through pointer
    _Bool arr[3] = {1, 0, 1};
    if (arr[0] != 1) return 3;
    if (arr[1] != 0) return 4;
    if (arr[2] != 1) return 5;
    return 0;
}
