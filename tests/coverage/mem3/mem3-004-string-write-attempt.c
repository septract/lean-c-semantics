// mem3-004-string-write-attempt.c
// Exercise select_ro_kind PrefStringLiteral in impl_mem.ml (L1704-1710)
// Writing to a string literal is UB but exercises the read-only check path
int main(void) {
    char *s = "hello";
    s[0] = 'H'; // UB: modifying string literal
    return 0;
}
