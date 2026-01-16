// Minimal test case from creduce for varargs bug (FIXED)
// Was: Lean reported out-of-bounds when Cerberus succeeded
// Root cause: longDouble was 16 bytes, should be 8 to match Cerberus
// Issue: accessing va_arg through a pointer to va_list
#include <stdarg.h>
va_list *pap;
void f8(int i, ...) {
  va_list a;
  va_start(a, i);
  pap = &a;
  va_arg(*pap, long double);
}
int main(void) { f8(0x4008, 14LL, 27.0); return 0; }
