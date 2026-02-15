// Test: access member of compound literal
// Exercises: PEmemberof — member access on compound literal value
struct S { int x; int y; };
int main(void) { return ((struct S){10, 20}).x - 10; }
