// mem3-003-const-compound-literal.c
// Exercise readonly_status PrefTemporaryLifetime in impl_mem.ml (L1325-1332)
int main(void) {
    const int *p = (const int[]){10, 20, 30};
    if (p[0] != 10) return 1;
    if (p[1] != 20) return 2;
    if (p[2] != 30) return 3;
    return 0;
}
