// Test: compound literal store_lock path
// Compound literals are stored then locked
int main(void) {
    int *p = (int[]){10, 20, 30};
    return p[0] + p[1] + p[2] - 60;
}
