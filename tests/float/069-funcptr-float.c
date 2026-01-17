// Test: function pointer returning float
float get_val(void) {
  return 42.0f;
}

int main(void) {
  float (*fp)(void) = get_val;
  float result = fp();
  return (result == 42.0f) ? 0 : 1;
}
