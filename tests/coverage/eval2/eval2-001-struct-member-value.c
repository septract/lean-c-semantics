// Test: access member of struct rvalue (not pointer)
// Exercises: PEmemberof — extracts member from struct VALUE, not pointer
struct S { int x; int y; };
struct S make(void) { struct S s = {10, 20}; return s; }
int main(void) { return make().x + make().y - 30; }
