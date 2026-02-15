// compound-006-shl-assign.c
// Exercise compound assignment <<= translation
int main(void) {
    int x = 1;
    x <<= 5;
    if (x != 32) return 1;
    return 0;
}
