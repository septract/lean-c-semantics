// CN test: Pre-increment and post-increment semantics
// From cn-tutorial: inc_1.c
// Tests: pre/post increment (++i vs i++), let bindings, casts, C assert
// NEEDS: spec let bindings, spec casts, typed literals

int inc_pre(int i)
/*@ requires
      let MAXi32 = 2147483647i64;
      (i64) i + 1i64 < MAXi32;
    ensures return == i + 1i32; @*/
{
  int start, pre;
  start = i;
  pre = ++i;
  return i;
}

int inc_post(int i)
/*@ requires
      let MAXi32 = 2147483647i64;
      (i64) i + 1i64 < MAXi32;
    ensures return == i + 1i32; @*/
{
  int start, pre;
  start = i;
  pre = i++;
  return i;
}

int main(void)
{
  return inc_pre(41);
}
