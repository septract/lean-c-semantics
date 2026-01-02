// Minimal: signed integer overflow (undefined behavior)
int main(void) {
  int x = 2147483647;  // INT_MAX
  return x + 1;  // UB: signed overflow
}
