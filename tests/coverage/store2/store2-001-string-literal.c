// Test: string literal store_lock path in impl_mem.ml
// String literals are stored then locked (read-only)
int main(void) {
    const char *s = "hello";
    return s[0] == 'h' && s[4] == 'o' ? 0 : 1;
}
