// Case 2: Runtime detection - both --exec and --pp=core succeed, UB at runtime
int main() {
    int x = 1;
    int y = 0;
    return x / y;
}
