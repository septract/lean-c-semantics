// Minimal: switch fallthrough
int main(void) {
  int x = 0;
  switch (1) {
    case 1:
      x += 10;
      // Fallthrough intentional
    case 2:
      x += 20;
      break;
  }
  return x; // 30
}
