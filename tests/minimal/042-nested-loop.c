// Minimal: nested loops
int main(void) {
  int sum = 0;
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 2; j++) {
      sum++;
    }
  }
  return sum;  // 6
}
