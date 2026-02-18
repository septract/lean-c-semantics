// io-003-printf-string.libc.c
// Exercise printf %s format conversion
#include <stdio.h>
int main(void) {
    const char *s = "world";
    printf("%s\n", s);
    return 0;
}
