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
    if (test_inline_mov_input(10) != 10) {return fail("test_inline_mov_input");}
    if (test_inline_mov_add_input(20) != 21) {return fail("test_inline_mov_add_input");}
    if (test_inline_mul_inputs(33, 1000) != 33000) {return fail("test_inline_mul_inputs");}
    if (test_inline_mov_mul_rax_100(44) != 4400) {return fail("test_inline_mov_mul_rax_100");}
// This test only succeeds on gcc >= 9 because of a bug in previous versions. 
// See comment in Vale.Test.Testinline.fst
//    if (test_inline_mov_add_input_dummy_mul(50) != 51) {return fail("test_inline_mov_add_input_dummy_mul");}
    if (test_inline_comment_add(4) != 8) {return fail("test_inline_comment_add");}
    if (test_inline_same_line(4) != 8) {return fail("test_inline_same_line");}
    if (test_inline_same_line_newline(4) != 12) {return fail("test_inline_same_line_newline");}
    return 0;
}
