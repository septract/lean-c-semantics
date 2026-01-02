// Minimal: goto statement
int main(void) {
  int x = 1;
  goto target;
  x = 999; // Skipped
target:
  return x; // 1
}
