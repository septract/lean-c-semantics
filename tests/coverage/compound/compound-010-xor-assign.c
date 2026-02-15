// compound-010-xor-assign.c
// Exercise compound assignment ^= translation
int main(void) {
    int x = 0xFF;
    x ^= 0x0F;
    if (x != 0xF0) return 1;
    return 0;
}
