// Test: read union member from union rvalue
// Exercises: PEmemberof — extracts member from union VALUE
union U { int i; char c; };
union U make(void) { union U u; u.i = 65; return u; }
int main(void) { return make().i - 65; }
