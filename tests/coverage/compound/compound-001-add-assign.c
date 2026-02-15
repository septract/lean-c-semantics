// compound-001-add-assign.c
// Exercise compound assignment += translation in translation.ml (L750-770)
int main(void) {
    int x = 10;
    x += 5;
    if (x != 15) return 1;
    x += -3;
    if (x != 12) return 2;
    return 0;
}
