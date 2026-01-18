// Test: no globals - just check starting address pattern
int main(void) {
    int x;  // local variable
    return (int)((unsigned long)&x & 0xFF);
}
