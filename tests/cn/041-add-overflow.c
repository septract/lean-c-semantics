// CN test: Addition with overflow protection via let bindings and casts
// From cn-tutorial: add_3.c
// Tests: let bindings in spec, integer casts (i64), typed integer literals
// NEEDS: spec let bindings, spec casts, typed literals (0i32, 2147483647i64)

signed int add_safe(signed int x, signed int y)
/*@ requires
      let MAXi32 = 2147483647i64;
      let MINi32 = -2147483648i64;
      let sum = (i64) x + (i64) y;
      MINi32 <= sum; sum <= MAXi32;
    ensures return == x + y; @*/
{
  signed int i;
  i = x + y;
  return i;
}

int main(void)
{
  return add_safe(20, 22);
}
