// Test: cast NULL pointer to int
// Expected: 0, no UB
int main(void) {
    int *p = 0;
    return (int)p;
}
