// Test: union store and load through the same member
// Audit: H1 - store should track lastUsedUnionMembers
union intfloat {
  int i;
  float f;
};

int main(void) {
  union intfloat u;
  u.i = 42;
  int result = u.i;  // Read back through same member
  return result;
}
