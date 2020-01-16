#include <stdio.h>
#include <stdint.h>
#include "vale_testInline.h"

int fail(char *s)
{
    printf("Vale TestInline failed: %s\n", s);
    return 1;
}

int main()
{
    if (test_inline1(33) != 3300) {return fail("test_inline1");}
    return 0;
}
