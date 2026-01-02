// Minimal: modulo by zero (undefined behavior)
int main(void) {
  int x = 10;
  int y = 0;
  return x % y;  // UB: modulo by zero
}
