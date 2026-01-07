// Minimal test - one int, return its address directly as long
int main(void) {
    int a;
    // Cast to unsigned long to avoid UB, then truncate
    return (int)((unsigned long)&a % 1000000);
}
