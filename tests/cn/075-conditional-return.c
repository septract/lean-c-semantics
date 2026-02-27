// From cn-tutorial: conditional return value with ternary in spec
int cond_1 (int i)
/*@ ensures
      return == (i == 0i32 ? 0i32 : 1i32); @*/
{
  if (i == 0) {
    return 0;
  } else {
    return 1;
  }
}
