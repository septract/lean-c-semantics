// Test: bitwise AND, OR, XOR operations (via C operators)
// These should use CivAND/CivOR/CivXOR paths in Core, NOT OpAnd/OpOr
// Audit: C2 - OpAnd/OpOr are boolean-only; bitwise uses different constructors
int main(void) {
  int a = 0xFF;   // 255
  int b = 0x0F;   // 15

  int and_result = a & b;   // 0x0F = 15
  int or_result  = a | b;   // 0xFF = 255
  int xor_result = a ^ b;   // 0xF0 = 240
  int not_result = ~b & 0xFF; // 0xF0 = 240

  // 15 + 255 + 240 + 240 = 750
  // Return mod 256 for exit code: 750 % 256 = 238
  return and_result + or_result;  // 15 + 255 = 270 % 256 = 14
}
