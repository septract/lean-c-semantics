// Test: double passed as function parameter
double identity_d(double x) {
  return x;
}

int main(void) {
  double a = 3.14159265358979;
  double b = identity_d(a);
  return (b == 3.14159265358979) ? 0 : 1;
}
