// Test: write float through pointer
int main(void) {
  float a = 0.0f;
  float *p = &a;
  *p = 7.25f;
  return (a == 7.25f) ? 0 : 1;
}
