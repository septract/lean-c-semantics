// Minimal: continue statement
int main(void) {
  int sum = 0;
  for (int i = 1; i <= 5; i++) {
    if (i == 3) {
      continue;
    }
    sum = sum + i;
  }
  return sum;  // 12 (1+2+4+5)
}
