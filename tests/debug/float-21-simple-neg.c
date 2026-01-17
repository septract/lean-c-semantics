// Test: !1.0f should be 0
int main(void) {
  float c = 1.0f;
  int nc = !c;  // nc should be 0
  return nc;    // should return 0
}
