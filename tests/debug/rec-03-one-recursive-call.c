// Single recursive call (depth 1)
int f(int n) {
  if (n == 0) {
    return 0;
  }
  return f(n - 1);  // Just recurse, no additional computation
}

int main(void) {
  return f(1);  // Expected: 0
}
