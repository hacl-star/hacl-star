#include <stdint.h>

extern const size_t chunk_size;
extern const size_t number_measurements;

// the return value of this function is discarded,
// it is there just to prevent the compiler from optimizing away
// this call
uint8_t do_one_computation(uint8_t *data);
void init_dut(void);
void prepare_inputs(uint8_t *input_data, uint8_t *classes);
