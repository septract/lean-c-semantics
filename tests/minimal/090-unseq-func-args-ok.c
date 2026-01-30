// Function arguments to different locations - NO RACE
int x = 0;
int y = 0;

int add(int a, int b) {
    return a + b;
}

int main(void) {
    return add(x = 1, y = 2);  // No race: different locations
}
