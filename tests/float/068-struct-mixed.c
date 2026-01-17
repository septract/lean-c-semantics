// Test: struct with mixed int and float
struct Mixed {
  int count;
  float value;
};

int main(void) {
  struct Mixed m;
  m.count = 10;
  m.value = 2.5f;
  float result = (float)m.count * m.value;
  return (result == 25.0f) ? 0 : 1;
}
