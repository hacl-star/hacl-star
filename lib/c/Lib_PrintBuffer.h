#include "stdint.h"
#include "stdio.h"
#include "stdbool.h"

void Lib_PrintBuffer_print_bytes(uint32_t len, uint8_t* buffer);
void Lib_PrintBuffer_print_compare(uint32_t len, uint8_t* buffer1, uint8_t* buffer2);
void Lib_PrintBuffer_print_compare_display(uint32_t len, uint8_t* buffer1, uint8_t* buffer2);
bool Lib_PrintBuffer_result_compare_display(uint32_t len, uint8_t* buffer1, uint8_t* buffer2);
