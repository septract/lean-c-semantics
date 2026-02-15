// Test: multiple string literal allocations with store_lock
int main(void) {
    const char *a = "abc";
    const char *b = "xyz";
    return a[0] == 'a' && b[2] == 'z' ? 0 : 1;
}
