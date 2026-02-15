// Test: post-increment in various expression contexts
int main(void) {
    int a = 0;
    int b = a++;    // SeqRMW, b=0, a=1
    int c = a++;    // SeqRMW, c=1, a=2
    int d = ++a;    // SeqRMW, d=3, a=3
    return b + c + d - 4;  // 0 + 1 + 3 = 4
}
