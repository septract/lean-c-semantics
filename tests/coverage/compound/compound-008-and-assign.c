// compound-008-and-assign.c
// Exercise compound assignment &= translation
int main(void) {
    int x = 0xFF;
    x &= 0x0F;
    if (x != 0x0F) return 1;
    return 0;
}
