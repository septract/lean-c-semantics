// Test: negative zero compares equal to positive zero
int main(void) {
  float pz = 0.0f;
  float nz = -0.0f;
  return (pz == nz) ? 0 : 1;
}
