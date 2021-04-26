#include <stdio.h>

#define printint(i) printf("%d\n", i);

/* This is a comment 123. */
int main(void)
{
    int integer = 123;
    int hex = 0xcafe;
    int negative = -69;
    float f = 1.23;
    char my_char = 'a';

    printint(integer);
    printf("hex: %x\n", hex);

    return 1;
}