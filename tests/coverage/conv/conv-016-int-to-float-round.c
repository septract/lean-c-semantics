// Test: int to float with precision loss
// Exercises: PEconv_int int-to-float (float has only 24-bit mantissa)
int main(void) {
  int x = 16777217;  // 2^24 + 1, not exactly representable as float
  float f = (float)x;
  // f rounds to 16777216.0f (2^24)
  int back = (int)f;
  return back == 16777216 ? 0 : 1;
}
