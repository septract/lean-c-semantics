// Case 1: Static rejection - both --exec and --pp=core fail
// This is a syntax/semantic error, not UB
int main() {
    return undefined_var;
}
