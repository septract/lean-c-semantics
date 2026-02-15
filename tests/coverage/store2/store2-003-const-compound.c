// Test: const compound literal store_lock
int main(void) {
    const int *p = (const int[]){100, 200};
    return p[0] == 100 && p[1] == 200 ? 0 : 1;
}
