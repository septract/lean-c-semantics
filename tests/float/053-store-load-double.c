// Test: double store/load roundtrip
int main(void) {
  double a = 3.14159265358979;
  double b = a;
  return (b == 3.14159265358979) ? 0 : 1;
}
