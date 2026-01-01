// Recursive function that adds 1 each level
int f(int n) {
  if (n == 0) {
    return 0;
  }
  return 1 + f(n - 1);
}

int main(void) {
  return f(3);  // Expected: 3
}
