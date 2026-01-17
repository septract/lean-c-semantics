// Test: force misaligned address by allocating padding first
// After allocating y, the next int should be at a non-8-byte-aligned address

struct S { float f; };

int main(void) {
  int y = 0;  // This pushes subsequent allocations down
  int i = 1;  // This should now be at a different alignment
  // Cast should trigger UB025 if &i is not 8-byte aligned
  struct S *p = (struct S *)&i;
  return 0;
}
