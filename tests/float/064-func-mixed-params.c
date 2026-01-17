// Test: function with mixed int and float parameters
float mixed(int a, float b) {
  return (float)a + b;
}

int main(void) {
  float result = mixed(2, 3.5f);
  return (result == 5.5f) ? 0 : 1;
}
