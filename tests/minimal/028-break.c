// Minimal: break statement
int main(void) {
  int i = 0;
  while (1) {
    i++;
    if (i == 5) {
      break;
    }
  }
  return i;  // 5
}
