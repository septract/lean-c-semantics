int test(float c) {
  // !c should be 0 (since c is non-zero)
  // !!c should be 1
  int nc = !c;     // nc = !1.0 = 0
  int nnc = !nc;   // nnc = !0 = 1
  return nnc;      // should return 1
}

int main(void) {
  return test(1.0f);
}
