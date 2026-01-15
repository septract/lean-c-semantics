// Test accessing argv[0] (program name)
// argv[0] is always "cmdname" (length 7) in Cerberus
int my_strlen(const char *s) {
    int len = 0;
    while (s[len] != '\0') {
        len++;
    }
    return len;
}

int main(int argc, char *argv[]) {
    // argc should be 1 (cmdname only)
    // argv[0] should be "cmdname" (length 7)
    return argc * 10 + my_strlen(argv[0]);  // Returns 17 (1*10 + 7)
}
