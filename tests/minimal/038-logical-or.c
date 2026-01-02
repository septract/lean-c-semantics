// Minimal: logical OR with short-circuit
int main(void) {
  int x = 0;
  // If short-circuit works, (x=1) is not evaluated.
  if (1 || (x = 1)) {
    return x;  // 0
  }
  return 100;
}
