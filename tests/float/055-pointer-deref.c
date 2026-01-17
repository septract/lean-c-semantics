// Test: float through pointer dereference
int main(void) {
  float a = 5.5f;
  float *p = &a;
  float b = *p;
  return (b == 5.5f) ? 0 : 1;
}
