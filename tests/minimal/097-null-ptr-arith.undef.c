// Test: pointer arithmetic on NULL is undefined behavior
// Audit: H2 - effArrayShiftPtrval on NULL returns NULL instead of error
int main(void) {
  int *p = (int *)0;  // NULL pointer
  int *q = p + 1;     // UB: arithmetic on NULL pointer
  return 0;
}
