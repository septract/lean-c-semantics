// compound-005-mod-assign.c
// Exercise compound assignment %= translation
int main(void) {
    int x = 47;
    x %= 10;
    if (x != 7) return 1;
    return 0;
}
