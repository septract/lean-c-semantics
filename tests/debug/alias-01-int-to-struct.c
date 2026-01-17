// Test: casting int* to struct* with float member
// Original: struct-aliasing-1.c from gcc-torture
// This tests type punning through pointer casts

struct S { float f; };

int foo(int *r, struct S *p) {
  int *q = (int *)&p->f;
  int i = *q;
  *r = 0;
  return i + *q;
}

int main(void) {
  int i = 1;
  // Cast &i (int*) to struct S* - potential alignment issue
  // since struct S has float member (8-byte aligned in Cerberus)
  // but int is only 4-byte aligned
  if (foo(&i, (struct S *)&i) != 1)
    return 1;
  return 0;
}
