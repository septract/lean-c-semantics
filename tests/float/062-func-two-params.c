// Test: function with two float parameters
float add(float x, float y) {
  return x + y;
}

int main(void) {
  float result = add(1.5f, 2.5f);
  return (result == 4.0f) ? 0 : 1;
}
