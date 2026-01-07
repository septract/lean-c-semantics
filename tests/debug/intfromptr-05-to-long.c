// Test: cast pointer to long
// Long should have enough range for any address
int main(void) {
    int a;
    return (int)(long)&a;  // Cast to long first (no UB), then truncate
}
