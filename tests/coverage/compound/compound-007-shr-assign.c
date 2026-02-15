// compound-007-shr-assign.c
// Exercise compound assignment >>= translation
int main(void) {
    int x = 256;
    x >>= 3;
    if (x != 32) return 1;
    return 0;
}
