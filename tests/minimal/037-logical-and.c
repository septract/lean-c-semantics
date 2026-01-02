// Minimal: logical AND with short-circuit
int main(void) {
  int x = 0;
  // If short-circuit works, (x=1) is not evaluated.
  if (0 && (x = 1)) {
    return 100;
  }
  return x;  // 0
}
