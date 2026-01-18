// Test: single char array - simplest case
char B[1];

int main(void) {
    return (int)((unsigned long)&B & 0xFF);
}
