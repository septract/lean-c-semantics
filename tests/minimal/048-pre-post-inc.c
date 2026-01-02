// Minimal: pre-increment vs post-increment
int main(void) {
  int x = 5;
  int y = x++; // y=5, x=6
  int z = ++x; // x=7, z=7
  return y + z; // 12
}
