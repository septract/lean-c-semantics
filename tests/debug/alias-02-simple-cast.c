// Test: simple pointer cast with alignment issue
// The float member requires 8-byte alignment but int is only 4-byte aligned

struct S { float f; };

int main(void) {
  int i = 1;
  // This cast should trigger UB025 if &i is not 8-byte aligned
  struct S *p = (struct S *)&i;
  // Just accessing p->f should be enough to trigger the UB
  // (the alignment check happens at the cast, not the access)
  return 0;
}
