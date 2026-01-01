// Minimal: while loop with accumulator
int main(void) {
  int sum = 0;
  int i = 1;
  while (i <= 5) {
    sum = sum + i;
    i = i + 1;
  }
  return sum;  // 15
}
