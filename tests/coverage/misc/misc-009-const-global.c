// misc-009-const-global.c
// Exercise store_lock for const globals in translation.ml (L4353,4360)
// Const-qualified global triggers pstore_lock instead of pstore
const int g_val = 42;
const int g_arr[3] = {10, 20, 30};
int main(void) {
    if (g_val != 42) return 1;
    if (g_arr[0] != 10) return 2;
    if (g_arr[1] != 20) return 3;
    if (g_arr[2] != 30) return 4;
    return 0;
}
