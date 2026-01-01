// Recursive multiply (simpler than factorial)
int f(int n) {
  if (n == 0) {
    return 1;
  }
  return 2 * f(n - 1);  // 2^n
}

int main(void) {
  return f(3);  // Expected: 8
}
