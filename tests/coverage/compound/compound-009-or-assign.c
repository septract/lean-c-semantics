// compound-009-or-assign.c
// Exercise compound assignment |= translation
int main(void) {
    int x = 0x0F;
    x |= 0xF0;
    if (x != 0xFF) return 1;
    return 0;
}
