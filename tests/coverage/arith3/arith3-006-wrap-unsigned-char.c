// arith3-006-wrap-unsigned-char.c
// Exercise mk_conv_int wrapI path (L79-80) for out-of-range conversions
int main(void) {
    // Out-of-range value wraps for unsigned char (0-255)
    unsigned char c1 = (unsigned char)256; // wraps to 0
    if (c1 != 0) return 1;
    unsigned char c2 = (unsigned char)300; // wraps to 44
    if (c2 != 44) return 2;
    unsigned char c3 = (unsigned char)-1;  // wraps to 255
    if (c3 != 255) return 3;
    // Out-of-range for unsigned short
    unsigned short s1 = (unsigned short)65536; // wraps to 0
    if (s1 != 0) return 4;
    return 0;
}
