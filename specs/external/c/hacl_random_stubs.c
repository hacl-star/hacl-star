#include <caml/mlvalues.h>
#include <caml/bigarray.h>

#include "Hacl_Unverified_Random.h"
CAMLprim value ml_randombytes(value buf) {
    randombytes(Caml_ba_data_val(buf),
                Caml_ba_array_val(buf)->dim[0]);
    return Val_unit;
}

